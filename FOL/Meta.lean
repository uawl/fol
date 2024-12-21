import FOL.Basic
import Lean.Environment
import Lean.Elab

namespace FOL

inductive Defs where
  | func (name : Name) (data : FuncData)
  | binder (name : Name) (data : BinderData)
  | rule (name : Name) (data : RuleType)
deriving Inhabited

def Env.addDef (e : Env) : Defs → Except String Env
  | .func n d => e.tryAddFunc n d
  | .binder n d => e.tryAddBinder n d
  | .rule n d => e.tryAddRule n d

namespace Meta

open Lean hiding HashMap
open Elab Command
open Std

initialize defsExt : PersistentEnvExtension Defs Defs (Array Defs × Env) ←
  registerPersistentEnvExtension {
    mkInitial := return (#[], {})
    addEntryFn := fun (a, e) d => (a.push d, e)
    addImportedFn := fun a => do
      let a := a.flatten
      match a.foldlM (·.addDef ·) { : Env } with
      | .ok e => return (#[], e)
      | .error e => throw <| IO.userError e
    exportEntriesFn := (·.1)
  }

private def addDef (stx : Syntax) (d : Defs) : CommandElabM Unit := do
  let (ds, e) := defsExt.getState (← getEnv)
  match e.addDef d with
  | .ok e =>
    modifyEnv (defsExt.setState · (ds.push d, e))
  | .error e =>
    throwErrorAt stx m!"{e}"

syntax mfuncData := "[" (ident " : " sepBy1(ident, " → ")),* "]"

@[specialize]
partial def parseFuncDatas (e : TSyntax ``mfuncData) : CommandElabM (Array MFuncData) := do
  match e with
  | `(mfuncData| [$[$mn : $ms→*],*]) =>
    let mn := mn.map (·.getId)
    let ms := ms.map (·.getElems.map (·.getId))
      |>.map (fun a => { argSorts := a.pop, resSort := a.back! : FuncData })
    return mn.zipWith ms (fun name d => { d with name})
  | _ => throwUnsupportedSyntax


declare_syntax_cat fol_term

syntax fol_args := "(" fol_term,* ")"

syntax "?" ident (fol_args)? : fol_term
syntax ident (fol_args)? : fol_term
syntax "\\" noWs ident ident ", " fol_term : fol_term

@[specialize]
partial def parseTermCore (e : TSyntax `fol_term) (depth : Nat) (aux : HashMap Name Nat) (auxm : HashMap Name Nat) (mdepth : Nat) : CommandElabM Term := do
  match e with
  | `(fol_term| ? $id $[($args,*)]?) =>
    let args := args.map (·.getElems) |>.getD #[]
    if let some idx := auxm[id.getId]? then
      return Term.mfunc (mdepth - (idx+1)) (← args.mapM (parseTermCore · depth aux auxm mdepth))
    else
      throwErrorAt e "unknown meta function"
  | `(fol_term| $id:ident $[($args,*)]?) =>
    if let some args := args then
      return Term.func id.getId (← args.getElems.mapM (parseTermCore · depth aux auxm mdepth))
    else if let some idx := aux[id.getId]? then
      return Term.bvar (depth - (idx+1))
    else
      return Term.func id.getId #[]
  | `(fol_term| \$n:ident $v:ident, $b) =>
    return Term.binder n.getId (← parseTermCore b (depth+1) (aux.insert v.getId depth) auxm mdepth)
  | _ => throwUnsupportedSyntax

@[inline] def parseTerm (e : TSyntax `fol_term) (auxm : HashMap Name Nat) (mdepth : Nat) : CommandElabM Term := do
  parseTermCore e 0 {} auxm mdepth


declare_syntax_cat fol_ruleType

syntax fol_term : fol_ruleType
syntax mfuncData " ⊢ " fol_term : fol_ruleType
syntax:50 fol_ruleType:51 " ⊢ " fol_ruleType:50 : fol_ruleType
syntax:50 mfuncData fol_ruleType:51 " ⊢ " fol_ruleType:50 : fol_ruleType
syntax "(" fol_ruleType ")" : fol_ruleType

@[specialize]
partial def parseRuleTypeCore (e : TSyntax `fol_ruleType) (depth : Nat) (auxm : HashMap Name Nat) : CommandElabM RuleType := do
  match e with
  | `(fol_ruleType| $p ⊢ $c) =>
    return RuleType.node {}  (← parseRuleTypeCore p depth auxm) (← parseRuleTypeCore c depth auxm)
  | `(fol_ruleType| $d:mfuncData $p ⊢ $c) =>
    let d ← parseFuncDatas d
    let auxm := auxm.insertMany <| d.mapIdx (fun i v => (v.name, i+depth))
    let depth := depth + d.size
    return RuleType.node { mfuncs := d }  (← parseRuleTypeCore p depth auxm) (← parseRuleTypeCore c depth auxm)
  | `(fol_ruleType| $t:fol_term) =>
    return RuleType.leaf {} (← parseTerm t auxm depth)
  | `(fol_ruleType| $d:mfuncData ⊢ $t:fol_term) =>
    let d ← parseFuncDatas d
    let auxm := auxm.insertMany <| d.mapIdx (fun i v => (v.name, i+depth))
    let depth := depth + d.size
    return RuleType.leaf { mfuncs := d } (← parseTerm t auxm depth)
  | `(fol_ruleType| ($r:fol_ruleType)) => parseRuleTypeCore r depth auxm
  | _ => throwErrorAt e "invalid rule type"

@[inline]
def parseRuleType (e : TSyntax `fol_ruleType) : CommandElabM RuleType :=
  parseRuleTypeCore e 0 {}

declare_syntax_cat fol_tac

syntax fol_tacSeq := sepBy1IndentSemicolon(fol_tac)

syntax applyArgs := "[" (("λ " ident,+ " => ")? fol_term ),* "]"

syntax "intro" : fol_tac
syntax "triv" : fol_tac
syntax "have " ident : fol_tac
syntax "done" : fol_tac
syntax "·" fol_tacSeq : fol_tac
syntax "specialize " num (applyArgs)? : fol_tac
syntax "apply " ident (applyArgs)? : fol_tac
syntax "probe" : fol_tac

def exceptToError : Except String α → CommandElabM α
  | .ok a => pure a
  | .error e => throwError e

def exceptToErrorAt (stx : Syntax) : Except String α → CommandElabM α
  | .ok a => pure a
  | .error e => throwErrorAt stx e

partial def elabTacs (tacs : TSyntaxArray `fol_tac) (ps : ProofState) : CommandElabM Unit := do
  let mut ps := ps
  for tac in tacs do
    match tac with
    | `(fol_tac| intro) => ps ← exceptToErrorAt tac ps.introduce
    | `(fol_tac| triv) => ps ← exceptToErrorAt tac ps.closeTrivial
    | `(fol_tac| have $n) =>
      ps ← exceptToErrorAt tac (ps.haveRule (defsExt.getState (← getEnv) |>.2) n.getId)
    | `(fol_tac| done) =>
      if !ps.isDone then
        throwErrorAt tac s!"unsolved goal: {ps}"
    | `(fol_tac| · $seq*) =>
      elabTacs seq.getElems (← exceptToErrorAt tac ps.focus)
      ps ← exceptToErrorAt tac ps.closeHead
    | `(fol_tac| specialize $i $[[$[$[λ $params,* =>]? $val],*]]?) =>
      let .ok mfuncs := ps.head.map (·.context.mfuncs)
        | throwErrorAt tac "no goals to solve"
      let md := mfuncs.size
      let mfuncs := mfuncs.mapIdx (fun i v => (v.name, i)) |> HashMap.empty.insertMany
      let params := params.getD #[]
        |>.map (·.map (·.getElems) |>.getD #[] |>.map (·.getId))
      let val := val.getD #[]
      let ts ← params.zipWith val (fun params val =>
        let depth := params.size
        let params := params.mapIdx (fun i p => (p, i)) |> HashMap.empty.insertMany
        parseTermCore val depth params mfuncs md) |>.mapM id
      ps ← exceptToErrorAt tac (ps.specialize i.getNat ts)
    | `(fol_tac| apply $n $[[$[$[λ $params,* =>]? $val],*]]?) =>
      let .ok mfuncs := ps.head.map (·.context.mfuncs)
        | throwErrorAt tac "no goals to solve"
      let md := mfuncs.size
      let mfuncs := mfuncs.mapIdx (fun i v => (v.name, i)) |> HashMap.empty.insertMany
      let params := params.getD #[]
        |>.map (·.map (·.getElems) |>.getD #[] |>.map (·.getId))
      let val := val.getD #[]
      let ts ← params.zipWith val (fun params val =>
        let depth := params.size
        let params := params.mapIdx (fun i p => (p, i)) |> HashMap.empty.insertMany
        parseTermCore val depth params mfuncs md) |>.mapM id
      ps ← exceptToErrorAt tac (ps.applyRule (defsExt.getState (← getEnv)).2 n.getId ts)
    | `(fol_tac| probe) =>
      logInfoAt tac s!"{ps}"
    | _ => throwUnsupportedSyntax
  if !ps.isDone then
    throwError s!"unsolved goal: {ps}"


syntax "fol_func " ident ("(" ident,* ")")? " : " ident : command
syntax "fol_binder " "\\" noWs ident ident ", " ident " : " ident : command
syntax "fol_rule " ident fol_ruleType : command
syntax "fol_prove " ident fol_ruleType " => " fol_tacSeq : command


elab_rules : command
  | `(fol_func%$tk $name:ident $[($params,*)]? : $res:ident) => do
    addDef tk (.func name.getId {
      argSorts := params.map (·.getElems) |>.getD #[] |>.map (·.getId)
      resSort := res.getId
    })
  | `(fol_binder%$tk \$n $v, $b : $r) => do
    addDef tk (.binder n.getId {
      varSort := v.getId
      bodySort := b.getId
      resSort := r.getId
    })
  | `(fol_rule%$tk $n $r) => do
    addDef tk (.rule n.getId (← parseRuleType r))
  | `(fol_prove%$tk $n $r => $t*) => do
    let n := n.getId
    let type ← parseRuleType r
    elabTacs t.getElems ⟨#[{ context.mfuncs := {}, context.premises := #[], goal := type }]⟩
    addDef tk (.rule n type)
