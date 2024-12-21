import Std.Data.HashMap
import Std.Data.HashSet

namespace FOL
open Std

export Lean (Name)

inductive Term where
  | mfunc (varName : Name) (idx : Nat) (args : Array Term)
  | bvar (idx : Nat)
  | func (name : Name) (args : Array Term)
  | binder (name : Name) (varName : Name) (body : Term)
deriving Inhabited, Repr

partial def Term.toStringCore (aux : Array Name) : Term → String
  | .mfunc v _ a => s!"{v}" ++ if a.isEmpty then "" else s!"({String.intercalate ", " (a.map (·.toStringCore aux)).toList})"
  | .bvar i => if let some n := aux[aux.size - (i + 1)]? then n.toString else s!"#{i}"
  | .func n a => s!"{n}" ++ if a.isEmpty then "" else s!"({String.intercalate ", " (a.map (·.toStringCore aux)).toList})"
  | .binder n v b => s!"\\{n} {v}, {b.toStringCore (aux.push v)}"

instance : ToString Term := ⟨Term.toStringCore #[]⟩

partial def Term.beq : Term → Term → Bool
  | .mfunc _ n₁ a₁, mfunc _ n₂ a₂ => n₁ == n₂ && (a₁.zipWith a₂ (·.beq ·)).all id
  | .bvar i, .bvar j => i == j
  | .func n₁ a₁, .func n₂ a₂ => n₁ == n₂ && (a₁.zipWith a₂ (·.beq ·)).all id
  | .binder n₁ _ b₁, .binder n₂ _ b₂ => n₁ == n₂ && b₁.beq b₂
  | _, _ => false

instance : BEq Term := ⟨Term.beq⟩

def Term.liftVar (n i : Nat) (k := 0) : Nat := if n < k then i else n + i

variable (n : Nat) in
partial def Term.liftN : Term → (k :_:= 0) → Term
  | .mfunc v n a, k => mfunc v n (a.map (·.liftN k))
  | .bvar i, k => .bvar (liftVar n i k)
  | .func n args, k => .func n (args.map (·.liftN k))
  | .binder n v b, k => .binder n v (b.liftN (k+1))

abbrev Term.lift := liftN 1

variable (k md : Nat) in
partial def Term.liftM : Term → Term
  | .mfunc v n a =>
    if n < md then
      .mfunc v n (a.map (·.liftM))
    else
      .mfunc v (n+k) (a.map (·.liftM))
  | .bvar i => .bvar i
  | .func n args => .func n (args.map (·.liftM))
  | .binder n v b => .binder n v b.liftM

partial def Term.inst : Term → Term → (k :_:=0) → Term
  | .mfunc v n a, e, k => mfunc v n (a.map (·.inst e k))
  | .bvar i, e, k =>
    if i < k then .bvar i
    else if i = k then liftN k e
    else .bvar (i-1)
  | .func n args, e, k =>
    .func n (args.map (·.inst e k))
  | .binder n v b, e, k =>
    .binder n v (b.inst e (k+1))


partial def Term.instMany : Term → Array Term → (k :_:= 0) → Term
  | .mfunc v n a, es, k => mfunc v n (a.map (·.instMany es k))
  | .bvar i, es, k =>
    if i < k then .bvar i
    else if i - k < es.size then liftN k es[es.size - (i - k + 1)]!
    else .bvar (i-es.size)
  | .func n args, e, k =>
    .func n (args.map (·.instMany e k))
  | .binder n v b, e, k =>
    .binder n v (b.instMany e (k+1))


partial def Term.instM : Term → Array Term → Nat → (k :_:= 0) → Term
  | .mfunc v n a, es, md, k =>
    if n < md then
      .mfunc v n (a.map (·.instM es md k))
    else if let some e := es[es.size-(n-md+1)]? then
      (e.liftM md 0 |>.instMany (a.map (·.instM es md k)))
    else mfunc v n (a.map (·.instM es md k))
  | .bvar i, _, _, _ => .bvar i
  | .func n args, es, md, k =>
    .func n (args.map (·.instM es md k))
  | .binder n v b, es, md, k =>
    .binder n v (b.instM es md (k+1))

structure FuncData where
  argSorts : Array Name
  resSort : Name
deriving Inhabited, Repr, BEq

def FuncData.toString : FuncData → String
  | { argSorts, resSort } => argSorts.foldl (· ++ ·.toString ++ " → ") "" ++ resSort.toString

instance : ToString FuncData := ⟨FuncData.toString⟩

structure BinderData where
  varSort : Name
  bodySort : Name
  resSort : Name
deriving Repr

structure MFuncData extends FuncData where
  name : Name
deriving Inhabited, Repr, BEq

structure RContext where
  mfuncs : Array MFuncData := #[]
deriving Inhabited, BEq, Repr


instance : ToString RContext where
  toString c :=
    let str := c.mfuncs
      |>.map (fun { name, toFuncData } => s!"{name} : {toFuncData}")
      |>.toList
      |> (String.intercalate "; ")
    s!"[{str}]"

inductive RuleType where
  | leaf (ctx : RContext) (conclusion : Term)
  | node (ctx : RContext) (premises conclusion : RuleType)
deriving Inhabited, Repr

def RuleType.beq : RuleType → RuleType → Bool
  | .leaf c₁ cl₁, .leaf c₂ cl₂ =>
    cl₁ == cl₂ && c₁ == c₂
  | .node ctx₁ p₁ c₁, .node ctx₂ p₂ c₂ => ctx₁ == ctx₂ && p₁.beq p₂ && c₁.beq c₂
  | _, _ => false

instance : BEq RuleType := ⟨RuleType.beq⟩

def RuleType.toString : RuleType → String
  | .leaf ctx c => s!"({ctx} ⊢ {c})"
  | .node c₁ p c => s!"({c₁} {p.toString} ⊢ {c.toString})"

instance : ToString RuleType := ⟨RuleType.toString⟩

variable (k : Nat) in
def RuleType.liftM : RuleType → (md :_:= 0) → RuleType
  | .leaf ctx c, md => .leaf ctx (c.liftM k (md + ctx.mfuncs.size))
  | .node ctx p c, md =>
    let md := md + ctx.mfuncs.size
    .node ctx (p.liftM md) (c.liftM md)

variable (fvarMap : Array Term) in
def RuleType.instM : RuleType → (k :_:= 0) → RuleType
  | .leaf ctx conclusion, k => .leaf ctx (conclusion.instM fvarMap (k + ctx.mfuncs.size))
  | .node c premise conclusion, k =>
    let k := k + c.mfuncs.size
    .node c (premise.instM k) (conclusion.instM k)

structure Env where
  funcs : HashMap Name FuncData := {}
  binders : HashMap Name BinderData := {}
  rules : HashMap Name RuleType := {}
deriving Repr, Inhabited


structure InferContext extends RContext where
  bvarSorts : Array Name

partial def inferSort (env : Env) (ctx : InferContext) (t : Term) : Except String Name := do
  go t ctx
where
  go t ctx := do
    match t with
    | .mfunc _ n as =>
      if let some { argSorts, resSort, name } := ctx.mfuncs[ctx.mfuncs.size - (n+1)]? then
        if as.size ≠ argSorts.size then
          throw s!"meta function '{name}' of {repr ctx.mfuncs} takes {argSorts.size} argument(s) but {as.size} provided"
        for i in [0:argSorts.size] do
          let argSort ← go as[i]! ctx
          if argSort ≠ argSorts[i]! then
            throw s!"sort mismatch '{argSort}' ≠ '{argSorts[i]!}'"
        return resSort
      else
        throw "unknown meta function"
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
    | .binder n _ b =>
      if let some { varSort, bodySort, resSort } := env.binders[n]? then
        let sort ← go b {ctx with bvarSorts := ctx.bvarSorts.push varSort }
        if sort ≠ bodySort then
          throw s!""
        return resSort
      else
        throw s!"unknown binder '{n}'"

def Env.tryAddFunc (e : Env) (name : Name) (data : FuncData) : Except String Env := do
  if e.funcs.contains name then
    throw s!"function '{name}' is already defined"
  return { e with funcs := e.funcs.insert name data }

def Env.tryAddBinder (e : Env) (name : Name) (data : BinderData) : Except String Env := do
  if e.binders.contains name then
    throw s!"binder '{name}' is already defined"
  return { e with binders := e.binders.insert name data }

def Env.tryAddRule (e : Env) (name : Name) (type : RuleType) : Except String Env := do
  if e.rules.contains name then
    throw s!"rule '{name}' is already defined"
  sortCheck { mfuncs := {} } type
  return { e with rules := e.rules.insert name type }
where
  sortCheck (aux : RContext)
  | .node ctx p c => sortCheck { mfuncs := aux.mfuncs ++ ctx.mfuncs } p *> sortCheck { mfuncs := aux.mfuncs ++ ctx.mfuncs } c
  | .leaf ctx c => discard <| inferSort e { mfuncs := aux.mfuncs ++ ctx.mfuncs, bvarSorts := #[] } c

structure ProofContext extends RContext where
  premises : Array RuleType
deriving Inhabited, Repr

def ProofContext.toString : ProofContext → String
  | { premises, mfuncs } =>
    "\n-- Premises --\n" ++
    ((premises.mapIdx (s!"{·}: {·}")).foldl (s!"{·}{·}\n") "") ++
    "-- Meta Functions --" ++
    mfuncs.foldl (fun l {name, toFuncData} => s!"{l}\n{name} : {toFuncData}") ""

instance : ToString ProofContext := ⟨ProofContext.toString⟩

structure ProofGoal where
  context : ProofContext
  goal : RuleType
deriving Repr, Inhabited

def ProofGoal.toString : ProofGoal → String
  | { context, goal } => s!"{context}\n-- Goal --\n{goal}"

instance : ToString ProofGoal := ⟨ProofGoal.toString⟩

def ProofGoal.isTrivial (goal : ProofGoal) : Bool :=
  goal.context.premises.any (fun g => g == goal.goal)

def ProofGoal.haveRule (goal : ProofGoal) (env : Env) (ruleName : Name) : Except String ProofGoal := do
  if let some type := env.rules[ruleName]? then
    return { goal with context.premises := goal.context.premises.push type }
  else throw s!"unknown rule '{ruleName}'"

def ProofGoal.introduce (goal : ProofGoal) : ProofGoal :=
  let (mfuncs, prems, newGoal) := collect goal.goal #[] #[] none
  { goal with
    context.mfuncs := goal.context.mfuncs ++ mfuncs
    context.premises := goal.context.premises.map (·.liftM mfuncs.size) ++ prems
    goal := newGoal }
where
  collect : RuleType → Array RuleType → Array MFuncData → Option Nat → Array MFuncData × Array RuleType × RuleType
    | .node {mfuncs} p c, aux, auxm, md => collect c (aux.push p) (auxm ++ mfuncs) (md.getD mfuncs.size)
    | .leaf {mfuncs} c, aux, auxm, md => (auxm ++ mfuncs, aux, .leaf {} (c.liftM (auxm.size + mfuncs.size - (md.getD mfuncs.size)) (md.getD mfuncs.size)))

def ProofGoal.specialize (goal : ProofGoal) (idx : Nat) (mfuncs : Array Term) : Except String (Array ProofGoal) := do
  if let some prem := goal.context.premises[idx]? then
    match prem with
    | .leaf ctx t =>
      unless ctx.mfuncs.size = mfuncs.size do
        throw "meta function size mismatch"
      return #[
        { goal with context.premises := goal.context.premises.push (.leaf {} (t.instM mfuncs mfuncs.size))}]
    | .node ctx p c =>
      unless ctx.mfuncs.size = mfuncs.size do
        throw "meta function size mismatch"
      return #[
        { goal with goal := (p.instM mfuncs mfuncs.size) },
        { goal with context.premises := goal.context.premises.push (c.instM mfuncs mfuncs.size)}]
  else throw s!"premise #{idx} doesn't exists"

partial def ProofGoal.applyRule (goal : ProofGoal) (env : Env) (name : Name) (mfuncs : Array Term) : Except String (Array ProofGoal) := do
  if let some rule := env.rules[name]? then
    let newGoals ← collect #[] mfuncs rule goal.goal
    return newGoals.map ({ goal with goal := · })
  else
    throw s!"unknown rule {name}"
where
  collect (aux : Array RuleType) (mfuncs : Array Term) : RuleType → RuleType → Except String (Array RuleType)
    | .leaf ctx t, .leaf ctx' t' => do
      unless ctx'.mfuncs.isEmpty do
        throw "goal has meta functions"
      unless ctx.mfuncs.size = mfuncs.size do
        throw "meta function size mismatch"
      let t := t.instM mfuncs 0
      unless t == t' do
        throw s!"failed to apply goal: {t} =?= {t'}"
      return aux
    | .node ctx p c, g => do
      unless ctx.mfuncs.size <= mfuncs.size do
        throw "meta function size mismatch"
      let mfuncCur := mfuncs.toSubarray.take ctx.mfuncs.size |>.toArray
      let p := p.instM mfuncCur
      let c := c.instM mfuncCur
      let aux := aux.push p
      collect aux (mfuncs.toSubarray.drop ctx.mfuncs.size |>.toArray) c g
    | _, .node _ _ _ =>
      throw "introduce goal first"


structure ProofState where
  goals : Array ProofGoal
deriving Repr

def ProofState.toString (ps : ProofState) : String :=
  ps.goals.foldl (fun l r => s!"{l}\n{r}") ""

instance : ToString ProofState := ⟨ProofState.toString⟩

def ProofState.isDone (ps : ProofState) : Bool := ps.goals.isEmpty

def ProofState.head (ps : ProofState) : Except String ProofGoal := do
  let some goal := ps.goals[0]?
    | throw "no goals to prove"
  return goal

def ProofState.closeHead (ps : ProofState) : Except String ProofState := do
  if h : 0 < ps.goals.size then
    return { ps with goals := ps.goals.eraseIdx 0 }
  else
    throw "no goals to prove"

def ProofState.replaceHead (ps : ProofState) (to : Array ProofGoal) : Except String ProofState := do
  if h : 0 < ps.goals.size then
    return { ps with goals := to ++ ps.goals.eraseIdx 0 }
  else
    throw "no goals to prove"

def ProofState.introduce (ps : ProofState) : Except String ProofState := do
  let goal ← ps.head
  ps.replaceHead #[goal.introduce]

def ProofState.closeTrivial (ps : ProofState) : Except String ProofState := do
  let goal ← ps.head
  if goal.isTrivial then
    ps.closeHead
  else
    throw "goal is not in the premises"

def ProofState.haveRule (ps : ProofState) (env : Env) (name : Name) : Except String ProofState := do
  let goal ← ps.head
  let newGoal ← goal.haveRule env name
  ps.replaceHead #[newGoal]

def ProofState.focus (ps : ProofState) : Except String ProofState := do
  let goal ← ps.head
  return { ps with goals := #[goal] }

def ProofState.specialize (ps : ProofState) (idx : Nat) (mfuncs : Array Term) : Except String ProofState := do
  let goal ← ps.head
  ps.replaceHead (← goal.specialize idx mfuncs)

def ProofState.applyRule (ps : ProofState) (env : Env) (name : Name) (mfuncs : Array Term) : Except String ProofState := do
  let goal ← ps.head
  ps.replaceHead (← goal.applyRule env name mfuncs)
