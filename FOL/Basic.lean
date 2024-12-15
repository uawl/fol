import Std.Data.HashMap
import Std.Data.HashSet

namespace FOL
open Std

export Lean (Name)

inductive Term where
  | fvar (name : Name)
  | bvar (idx : Nat)
  | func (name : Name) (args : Array Term)
  | binder (name : Name) (body : Term)
deriving Inhabited

partial def Term.toString : Term → String
  | .fvar n => s!"${n}"
  | .bvar i => s!"#{i}"
  | .func n a => s!"{n}({String.intercalate ", " (a.map (·.toString)).toList})"
  | .binder n b => s!"(!{n}, {b.toString})"

instance : ToString Term := ⟨Term.toString⟩
instance : Repr Term where
  reprPrec t _ := toString t

partial def Term.beq : Term → Term → Bool
  | .fvar n, .fvar m => n == m
  | .bvar i, .bvar j => i == j
  | .func n₁ a₁, .func n₂ a₂ => n₁ == n₂ && (a₁.zipWith a₂ (·.beq ·)).all id
  | .binder n₁ b₁, .binder n₂ b₂ => n₁ == n₂ && b₁.beq b₂
  | _, _ => false

instance : BEq Term := ⟨Term.beq⟩

def Term.liftVar (n i : Nat) (k := 0) : Nat := if n < k then i else n + i

variable (n : Nat) in
partial def Term.liftN : Term → (k :_:= 0) → Term
  | .fvar n, _ => .fvar n
  | .bvar i, k => .bvar (liftVar n i k)
  | .func n args, k => .func n (args.map (·.liftN k))
  | .binder n b, k => .binder n (b.liftN (k+1))

abbrev Term.lift := liftN 1

partial def Term.inst : Term → Term → (k :_:=0) → Term
  | .fvar n, _, _ => .fvar n
  | .bvar i, e, k =>
    if i < k then .bvar i
    else if i = k then liftN k e
    else .bvar (i-1)
  | .func n args, e, k =>
    .func n (args.map (·.inst e k))
  | .binder n b, e, k =>
    .binder n (b.inst e (k+1))

partial def Term.instFree : Term → HashMap Name Term → (k :_:= 0) → Term
  | .fvar n, es, k =>
    if let some e := es[n]? then liftN k e else .fvar n
  | .bvar i, _, _ => .bvar i
  | .func n args, es, k =>
    .func n (args.map (·.instFree es k))
  | .binder n b, es, k =>
    .binder n (b.instFree es (k+1))

structure FuncData where
  argSorts : Array Name
  resSort : Name
deriving Repr

structure BinderData where
  varSort : Name
  bodySort : Name
  resSort : Name
deriving Repr

inductive RuleType where
  | leaf (conclusion : Term)
  | node (premises conclusion : RuleType)
deriving BEq

def RuleType.toString : RuleType → String
  | .leaf c => s!"{c}"
  | .node p c => s!"({p.toString} ⊢ {c.toString})"

instance : ToString RuleType := ⟨RuleType.toString⟩

instance : Repr RuleType where
  reprPrec t _ := t.toString

variable (fvarMap : HashMap Name Term) in
def RuleType.instFree : RuleType → RuleType
  | .leaf conclusion => .leaf (conclusion.instFree fvarMap)
  | .node premise conclusion => .node premise.instFree conclusion.instFree

structure RuleData where
  fvarSorts : HashMap Name Name
  type : RuleType
deriving Repr

structure Env where
  funcs : HashMap Name FuncData := {}
  binders : HashMap Name BinderData := {}
  rules : HashMap Name RuleData := {}
deriving Repr

def Env.tryAddFunc (e : Env) (name : Name) (data : FuncData) : Except String Env := do
  if e.funcs.contains name then
    throw "function '{name}' is already defined"
  return { e with funcs := e.funcs.insert name data }

def Env.tryAddBinder (e : Env) (name : Name) (data : BinderData) : Except String Env := do
  if e.binders.contains name then
    throw "binder '{name}' is already defined"
  return { e with binders := e.binders.insert name data }

def Env.tryAddRule (e : Env) (name : Name) (data : RuleData) : Except String Env := do
  if e.rules.contains name then
    throw "rule '{name}' is already defined"
  return { e with rules := e.rules.insert name data }


structure Context where
  fvarSorts : HashMap Name Name
deriving Repr

structure InferContext extends Context where
  bvarSorts : Array Name := {}

partial def inferSort (env : Env) (ctx : InferContext) (t : Term) : Except String Name := do
  go t ctx
where
  go t ctx := do
    match t with
    | .fvar n =>
      if let some sort := ctx.fvarSorts[n]? then
        return sort
      else
        throw "unknown free variable"
    | .bvar i =>
      if i < ctx.bvarSorts.size then
        return ctx.bvarSorts[ctx.bvarSorts.size - (i+1)]!
      else
        throw s!"unexpected bounded variable {i}"
    | .func n as =>
      if let some { argSorts, resSort } := env.funcs[n]? then
        if argSorts.size ≠ as.size then
          throw s!"function '{n}' takes {argSorts.size} argument(s) but {as.size} provided"
        for i in [0:argSorts.size] do
          let argSort ← go as[i]! ctx
          if argSort ≠ argSorts[i]! then
            throw s!"sort mismatch '{argSort}' ≠ '{argSorts[i]!}'"
        return resSort
      else
        throw s!"unknown function '{n}'"
    | .binder n b =>
      if let some { varSort, bodySort, resSort } := env.binders[n]? then
        let sort ← go b {ctx with bvarSorts := ctx.bvarSorts.push varSort }
        if sort ≠ bodySort then
          throw s!""
        return resSort
      else
        throw s!"unknown binder '{n}'"

structure ProofContext extends Context where
  premises : Array RuleType

def ProofContext.toString : ProofContext → String
  | { premises, fvarSorts } =>
    "\n-- Premises --\n" ++
    premises.foldl (s!"{·}{·}\n") "" ++
    "-- Variables --" ++
    fvarSorts.fold (fun l n t => s!"{l}\n{n} : {t}") ""

instance : Repr ProofContext where
  reprPrec r _ := r.toString

structure ProofGoal where
  context : ProofContext
  goal : RuleType
deriving Repr

def ProofGoal.isTrivial (goal : ProofGoal) : Bool :=
  goal.context.premises.any (· == goal.goal)

def ProofGoal.applyRule (goal : ProofGoal) (env : Env) (ruleName : Name) (fvarMap : HashMap Name Term) : Except String (Array ProofGoal) := do
  if let some { fvarSorts, type } := env.rules[ruleName]? then
    for (id, sort) in fvarSorts do
      let some e := fvarMap[id]?
        | throw s!"variable {id} of rule {ruleName} is not provided"
      let fvarSort ← inferSort env { goal.context.toContext with } e
      unless sort = fvarSort do
        throw s!"sort mismatch {fvarSort} ≠ {sort}"
    let type := type.instFree fvarMap
    let premises ← findPremises type goal.goal #[]
    return premises.map ({ context := goal.context, goal := · })
  else throw s!"unknown rule '{ruleName}'"
where
  findPremises : RuleType → RuleType → Array RuleType → Except String (Array RuleType)
  | .leaf t, .leaf t', aux => if t == t' then return aux else throw s!"failed to apply rule: {t} =?= {t'}"
  | src@(.node p c), tgt, aux =>
    if src == tgt then
      return aux
    else
      findPremises c tgt (aux.push p)
  | src, tgt, _ => throw s!"failed to apply rule: {src} =?= {tgt}"

structure ProofState where
  goals : Array ProofGoal

def testEnv := { : Env}
  |>.tryAddFunc `imp { argSorts := #[`wff, `wff], resSort := `wff }
  |>.bind (·.tryAddRule `ax.mp {
      fvarSorts := HashMap.ofList [(`φ, `wff), (`ψ, `wff)]
      type := .node (.leaf (.fvar `φ)) (.node (.leaf (.func `imp #[(.fvar `φ), (.fvar `ψ)])) (.leaf (.fvar `ψ)))
    })
  |>.toOption
  |>.getD { : Env}

#eval ProofGoal.applyRule { context := { fvarSorts := HashMap.ofList [(`φ, `wff), (`ψ, `wff), (`χ, `wff)], premises := #[] }, goal := .leaf (.fvar `χ) } testEnv `ax.mp (HashMap.ofList [(`φ, .fvar `ψ), (`ψ, .fvar `χ)])
