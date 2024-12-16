import Std.Data.HashMap
import Std.Data.HashSet

namespace FOL
open Std

export Lean (Name)

inductive Term where
  | mfunc (name : Name) (args : Array Term)
  | bvar (idx : Nat)
  | func (name : Name) (args : Array Term)
  | binder (name : Name) (body : Term)
deriving Inhabited

partial def Term.toString : Term → String
  | .mfunc n a => s!"%{n}" ++ if a.isEmpty then "" else s!"({String.intercalate ", " (a.map (·.toString)).toList})"
  | .bvar i => s!"#{i}"
  | .func n a => s!"{n}" ++ if a.isEmpty then "" else s!"({String.intercalate ", " (a.map (·.toString)).toList})"
  | .binder n b => s!"\\{n}, {b.toString}"

instance : ToString Term := ⟨Term.toString⟩
instance : Repr Term where
  reprPrec t _ := toString t

partial def Term.beq : Term → Term → Bool
  | .mfunc n₁ a₁, mfunc n₂ a₂ => n₁ == n₂ && (a₁.zipWith a₂ (·.beq ·)).all id
  | .bvar i, .bvar j => i == j
  | .func n₁ a₁, .func n₂ a₂ => n₁ == n₂ && (a₁.zipWith a₂ (·.beq ·)).all id
  | .binder n₁ b₁, .binder n₂ b₂ => n₁ == n₂ && b₁.beq b₂
  | _, _ => false

instance : BEq Term := ⟨Term.beq⟩

def Term.liftVar (n i : Nat) (k := 0) : Nat := if n < k then i else n + i

variable (n : Nat) in
partial def Term.liftN : Term → (k :_:= 0) → Term
  | .mfunc n a, _ => mfunc n a
  | .bvar i, k => .bvar (liftVar n i k)
  | .func n args, k => .func n (args.map (·.liftN k))
  | .binder n b, k => .binder n (b.liftN (k+1))

abbrev Term.lift := liftN 1

partial def Term.inst : Term → Term → (k :_:=0) → Term
  | .mfunc n a, _, _ => mfunc n a
  | .bvar i, e, k =>
    if i < k then .bvar i
    else if i = k then liftN k e
    else .bvar (i-1)
  | .func n args, e, k =>
    .func n (args.map (·.inst e k))
  | .binder n b, e, k =>
    .binder n (b.inst e (k+1))

partial def Term.instMany : Term → Array Term → (k :_:= 0) → Term
  | .mfunc n a, _, _ => mfunc n a
  | .bvar i, es, k =>
    if i < k then .bvar i
    else if i - k < es.size then liftN k es[es.size - (i - k + 1)]!
    else .bvar (i-es.size)
  | .func n args, e, k =>
    .func n (args.map (·.instMany e k))
  | .binder n b, e, k =>
    .binder n (b.instMany e (k+1))

partial def Term.instFree : Term → HashMap Name Term → (k :_:= 0) → Term
  | .mfunc n a, es, k =>
    if let some e := es[n]? then liftN k (e.instMany a) else mfunc n a
  | .bvar i, _, _ => .bvar i
  | .func n args, es, k =>
    .func n (args.map (·.instFree es k))
  | .binder n b, es, k =>
    .binder n (b.instFree es (k+1))

structure FuncData where
  argSorts : Array Name
  resSort : Name
deriving Repr

def FuncData.toString : FuncData → String
  | { argSorts, resSort } => argSorts.foldl (· ++ ·.toString ++ " → ") "" ++ resSort.toString

instance : ToString FuncData := ⟨FuncData.toString⟩

structure BinderData where
  varSort : Name
  bodySort : Name
  resSort : Name
deriving Repr

inductive RuleType where
  | leaf (conclusion : Term)
  | node (premises conclusion : RuleType)
deriving BEq, Inhabited

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
  mfuncs : HashMap Name FuncData
  type : RuleType
deriving Repr

structure Env where
  funcs : HashMap Name FuncData := {}
  binders : HashMap Name BinderData := {}
  rules : HashMap Name RuleData := {}
deriving Repr

structure Context where
  mfuncs : HashMap Name FuncData
deriving Repr, Inhabited

structure InferContext extends Context where
  bvarSorts : Array Name

partial def inferSort (env : Env) (ctx : InferContext) (t : Term) : Except String Name := do
  go t ctx
where
  go t ctx := do
    match t with
    | .mfunc n as =>
      if let some { argSorts, resSort } := ctx.mfuncs[n]? then
        if as.size ≠ argSorts.size then
          throw s!"meta function '{n}' takes {argSorts.size} argument(s) but {as.size} provided"
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
    | .binder n b =>
      if let some { varSort, bodySort, resSort } := env.binders[n]? then
        let sort ← go b {ctx with bvarSorts := ctx.bvarSorts.push varSort }
        if sort ≠ bodySort then
          throw s!""
        return resSort
      else
        throw s!"unknown binder '{n}'"

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
  sortCheck data.type
  return { e with rules := e.rules.insert name data }
where
  sortCheck
  | .node p c => sortCheck p *> sortCheck c
  | .leaf c => discard <| inferSort e { mfuncs := data.mfuncs, bvarSorts := #[] } c

structure ProofContext extends Context where
  premises : Array RuleType
deriving Inhabited

def ProofContext.toString : ProofContext → String
  | { premises, mfuncs } =>
    "\n-- Premises --\n" ++
    ((premises.mapIdx (s!"{·}: {·}")).foldl (s!"{·}{·}\n") "") ++
    "-- Meta Functions --" ++
    mfuncs.fold (fun l n t => s!"{l}\n{n} : {t}") ""

instance : ToString ProofContext := ⟨ProofContext.toString⟩

instance : Repr ProofContext where
  reprPrec r _ := r.toString

structure ProofGoal where
  context : ProofContext
  goal : RuleType
deriving Repr, Inhabited

def ProofGoal.toString : ProofGoal → String
  | { context, goal } => s!"{context}\n-- Goal --\n{goal}"

instance : ToString ProofGoal := ⟨ProofGoal.toString⟩

def ProofGoal.isTrivial (goal : ProofGoal) : Bool :=
  goal.context.premises.any (· == goal.goal)

def ProofGoal.applyRule (goal : ProofGoal) (env : Env) (ruleName : Name) (mfuncMap : HashMap Name Term) : Except String (Array ProofGoal) := do
  if let some { mfuncs, type } := env.rules[ruleName]? then
    for (id, { argSorts, resSort }) in mfuncs do
      let some e := mfuncMap[id]?
        | throw s!"variable {id} of rule {ruleName} is not provided"
      let resSort' ← inferSort env { goal.context.toContext with bvarSorts := argSorts } e
      unless resSort = resSort' do
        throw s!"sort mismatch {resSort'} ≠ {resSort}"
    let type := type.instFree mfuncMap
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

def ProofGoal.applyPremise (goal : ProofGoal) (idx : Nat) : Except String (Array ProofGoal) := do
  if let some type := goal.context.premises[idx]? then
    let premises ← findPremises type goal.goal #[]
    return premises.map ({ context := goal.context, goal := · })
  else throw s!"premises index {idx} out of bound"
where
  findPremises : RuleType → RuleType → Array RuleType → Except String (Array RuleType)
  | .leaf t, .leaf t', aux => if t == t' then return aux else throw s!"failed to apply rule: {t} =?= {t'}"
  | src@(.node p c), tgt, aux =>
    if src == tgt then
      return aux
    else
      findPremises c tgt (aux.push p)
  | src, tgt, _ => throw s!"failed to apply premise: {src} =?= {tgt}"


def ProofGoal.introduce (goal : ProofGoal) : ProofGoal :=
  let (prems, newGoal) := collect goal.goal #[]
  { goal with context.premises := goal.context.premises ++ prems, goal := newGoal }
where
  collect : RuleType → Array RuleType → Array RuleType × RuleType
    | .node p c, aux => collect c (aux.push p)
    | .leaf c, aux => (aux, .leaf c)


structure ProofState where
  goals : Array ProofGoal
