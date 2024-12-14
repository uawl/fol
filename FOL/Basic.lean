import Std.Data.HashMap
import Std.Data.HashSet

namespace FOL
open Std

export Lean (Name)

inductive Term where
  | bvar (idx : Nat)
  | func (name : Name) (args : Array Term)
  | binder (name : Name) (body : Term)
deriving Inhabited, Repr

partial def Term.beq : Term → Term → Bool
  | .bvar i, .bvar j => i == j
  | .func n₁ a₁, .func n₂ a₂ => n₁ == n₂ && (a₁.zipWith a₂ (·.beq ·)).all id
  | .binder n₁ b₁, .binder n₂ b₂ => n₁ == n₂ && b₁.beq b₂
  | _, _ => false

instance : BEq Term := ⟨Term.beq⟩

def Term.liftVar (n i : Nat) (k := 0) : Nat := if n < k then i else n + i

variable (n : Nat) in
partial def Term.liftN : Term → (k :_:= 0) → Term
  | .bvar i, k => .bvar (liftVar n i k)
  | .func n args, k => .func n (args.map (·.liftN k))
  | .binder n b, k => .binder n (b.liftN (k+1))

abbrev Term.lift := liftN 1

partial def Term.inst : Term → Term → (k :_:=0) → Term
  | .bvar i, e, k =>
    if i < k then .bvar i
    else if i = k then liftN k e
    else .bvar (i-1)
  | .func n args, e, k =>
    .func n (args.map (·.inst e k))
  | .binder n b, e, k =>
    .binder n (b.inst e (k+1))

partial def Term.instFree : Term → Array Term → (k :_:= 0) → Term
  | .bvar i, es, k =>
    if i < k then .bvar i
    else if h : i - k < es.size then liftN k es[es.size - (i - k + 1)]
    else .bvar i
  | .func n args, es, k =>
    .func n (args.map (·.instFree es k))
  | .binder n b, es, k =>
    .binder n (b.instFree es (k+1))

structure FuncData where
  argSorts : Array Name
  resSort : Name
deriving Repr

structure JudgementData where
  argSorts : Array Name
deriving Repr

structure BinderData where
  varSort : Name
  bodySort : Name
  resSort : Name
deriving Repr

structure Judgement where
  name : Name
  args : Array Term
deriving BEq, Repr

structure RuleData where
  fvarSorts : Array Name
  premises : Array Judgement
  conclusion : Judgement
deriving Repr

structure Env where
  funcs : HashMap Name FuncData := {}
  judgements : HashMap Name JudgementData := {}
  binders : HashMap Name BinderData := {}
  rules : HashMap Name RuleData := {}
deriving Repr

def Env.tryAddFunc (e : Env) (name : Name) (data : FuncData) : Except String Env := do
  if e.funcs.contains name then
    throw "function '{name}' is already defined"
  return { e with funcs := e.funcs.insert name data }

def Env.tryAddJudgement (e : Env) (name : Name) (data : JudgementData) : Except String Env := do
  if e.judgements.contains name then
    throw "judgement '{name}' is already defined"
  return { e with judgements := e.judgements.insert name data }

def Env.tryAddBinder (e : Env) (name : Name) (data : BinderData) : Except String Env := do
  if e.binders.contains name then
    throw "binder '{name}' is already defined"
  return { e with binders := e.binders.insert name data }

def Env.tryAddRule (e : Env) (name : Name) (data : RuleData) : Except String Env := do
  if e.rules.contains name then
    throw "rule '{name}' is already defined"
  return { e with rules := e.rules.insert name data }


structure Context where
  bvarSorts : Array Name
deriving Repr

partial def inferSort (env : Env) (ctx : Context) (t : Term) : Except String Name := do
  go t ctx
where
  go t ctx := do
    match t with
    | .bvar i =>
      if i < ctx.bvarSorts.size then
        return ctx.bvarSorts[ctx.bvarSorts.size - (i+1)]!
      else
        throw s!"term has a free variable #{i - ctx.bvarSorts.size}"
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

def Judgement.instFree (j : Judgement) (fvarArr : Array Term) : Except String Judgement := do
  return { j with args := j.args.map (·.instFree fvarArr) }


structure ProofContext extends Context where
  premises : Array Judgement
deriving Repr

structure ProofGoal where
  context : ProofContext
  goal : Judgement
deriving Repr

def ProofGoal.useRule (goal : ProofGoal) (env : Env) (ruleName : Name) (fvarArr : Array Term) : Except String (Array ProofGoal) := do
  if let some rule := env.rules[ruleName]? then
    unless rule.fvarSorts.size = fvarArr.size do
      throw s!"rule '{ruleName}' has {rule.fvarSorts.size} free variable(s) but {fvarArr.size} provided"
    for i in [0:fvarArr.size] do
      let fvarSort ← inferSort env goal.context.toContext fvarArr[i]!
      unless rule.fvarSorts[i]! = fvarSort do
        throw s!"sort mismatch {fvarSort} ≠ {rule.fvarSorts[i]!}"
    let conclusion ← rule.conclusion.instFree fvarArr
    if goal.goal != conclusion then
      throw s!"goal mismatch {repr goal.goal} ≠ {repr conclusion}"
    let premises ← rule.premises.mapM (·.instFree fvarArr)
    return premises.map ({ context := goal.context, goal := · })
  else throw s!"unknown rule '{ruleName}'"

structure ProofState where
  goals : Array ProofGoal

def testEnv := { : Env}
  |>.tryAddJudgement `tru { argSorts := #[`wff] }
  |>.bind (·.tryAddFunc `imp { argSorts := #[`wff, `wff], resSort := `wff })
  |>.bind (·.tryAddRule `ax.mp {
      fvarSorts := #[`wff, `wff]
      premises := #[{ name := `tru, args := #[.bvar 1] }, { name := `tru, args := #[.func `imp #[.bvar 1, .bvar 0]] }]
      conclusion := { name := `tru, args := #[.bvar 0] } })
  |>.toOption
  |>.getD { : Env}

#eval ProofGoal.useRule { context := { bvarSorts := #[`wff, `wff, `wff], premises := #[] }, goal := { name := `tru, args := #[.bvar 2]} } testEnv `ax.mp #[.bvar 1, .bvar 2]
