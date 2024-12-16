import FOL.Basic
import FOL.Parser

open FOL Std

inductive Command where
  | addFunc (name : Name) (data : FuncData)
  | addBinder (name : Name) (data : BinderData)
  | addRule (name : Name) (data : RuleData)
  | checkEnv
  | prove (name : Name) (data : RuleData)

inductive Tactic where
  | trivial
  | introduce
  | applyRule (ruleName : Name) (mfuncMap : HashMap Name Term)
  | applyPremise (idx : Nat)

namespace Frontend
open FOL.Parser Parser Char

def parseAddFunc : Parser Command := do
  let id ← ident <* ws
  let args ← option? <| char '(' *> ws *> sepBy (char ',' <* ws) (ident <* ws) <* ws <* char ')' <* ws
  let args := args.getD #[]
  let _ ← char ':' <* ws
  let res ← ident
  return .addFunc id.toName { argSorts := args.map (·.toName), resSort := res.toName }

def parseAddBinder : Parser Command := do
  let id ← ident <* ws
  let var ← ident <* ws
  let body ← ident <* ws
  let res ← ident <* ws
  return .addBinder id.toName { varSort := var.toName, bodySort := body.toName, resSort := res.toName }

def parseAddRule : Parser Command := do
  let id ← ident <* ws1
  let mfuncs ← option? do
    let _ ← char '['
    let funcs ← sepBy (char ',' <* ws) do
      let name ← ident <* ws
      let _ ← char ':' <* ws
      let data ← funcData <* ws
      return (name.toName, data)
    let _ ← char ']' <* ws
    return funcs
  let mfuncs := mfuncs.getD #[] |>.toList |> HashMap.ofList
  let type ← ruleType
  return .addRule id.toName { mfuncs, type }

def parseProve : Parser Command := do
  let id ← ident <* ws1
  let mfuncs ← option? do
    let _ ← char '['
    let funcs ← sepBy (char ',' <* ws) do
      let name ← ident <* ws
      let _ ← char ':' <* ws
      let data ← funcData <* ws
      return (name.toName, data)
    let _ ← char ']' <* ws
    return funcs
  let mfuncs := mfuncs.getD #[] |>.toList |> HashMap.ofList
  let type ← ruleType
  return .prove id.toName { mfuncs, type }

def parseCommand : Parser Command := do
  let cmd ← ws *> ident <* ws
  match cmd with
  | "add_func" => parseAddFunc
  | "prove" => parseProve
  | "add_binder" => parseAddBinder
  | "add_rule" => parseAddRule
  | "check_env" => return .checkEnv
  | cmd => throwUnexpectedWithMessage (msg := s!"unknown command {cmd}")

def parseApply : Parser Tactic := do
  if let some idx ← option? nat then
    return .applyPremise idx
  else
    let id ← ident <* ws
    let mfuncsMap ← option? do
      let _ ← char '[' <* ws
      let map ← sepBy (char ',' <* ws) do
        let k ← ident <* ws
        let _ ← chars "<-" <* ws
        let v ← term <* ws
        return (k.toName, v)
      let _ ← char ']' <* ws
      return map
    let mfuncsMap := HashMap.empty.insertMany (mfuncsMap.getD #[])
    return .applyRule id.toName mfuncsMap

def parseTactic : Parser Tactic := do
  let tac ← ws *> ident <* ws
  match tac with
  | "introduce" => return .introduce
  | "trivial" => return .trivial
  | "apply" => parseApply
  | tac => throwUnexpectedWithMessage (msg := s!"unknown tactic {tac}")


end Frontend

open Frontend

partial def proveLoop (env : Env) (id : Name) (s : ProofState) : IO Unit := do
  if s.goals.size = 0 then
    println! "proof complete: {id}"
    return
  IO.print s!"\x1B[2J\x1B[H"
  s.goals.forRevM (fun goal => do
    println! "{goal}"
  )
  IO.print s!"{id}> "
  let stdin ← IO.getStdin
  let line ← stdin.getLine
  let s ← (do
    match parseTactic.run line with
    | .ok _ .introduce =>
      return { s with goals := s.goals.map (·.introduce) }
    | .ok _ .trivial =>
      return { s with goals := s.goals.filter (!·.isTrivial) }
    | .ok _ (.applyRule n m) =>
      match s.goals[0]!.applyRule env n m with
      | .ok newGoals => return { s with goals := newGoals ++ s.goals.eraseIdx! 0 }
      | .error e =>
        IO.eprintln e
        return s
    | .ok _ (.applyPremise i) =>
      match s.goals[0]!.applyPremise i with
      | .ok newGoals => return { s with goals := newGoals ++ s.goals.eraseIdx! 0 }
      | .error e =>
        IO.eprintln e
        return s
    | .error _ e =>
      IO.eprintln s!"parse error: {e}"
      return s
  )
  proveLoop env id s


def main : IO Unit := do
  let mut env := { : Env}
  let stdin ← IO.getStdin
  repeat do
    IO.print "FOL> "
    let line ← stdin.getLine
    match parseCommand.run line with
    | .ok _ (.addFunc n d) =>
      match env.tryAddFunc n d with
      | .ok env' => env := env'
      | .error e => IO.eprintln e
    | .ok _ (.addBinder n d) =>
      match env.tryAddBinder n d with
      | .ok env' => env := env'
      | .error e => IO.eprintln e
    | .ok _ (.addRule n d) =>
      match env.tryAddRule n d with
      | .ok env' => env := env'
      | .error e => IO.eprintln e
    | .ok _ (.prove n d) =>
      if let .error e := env.tryAddRule n d then
        IO.eprintln e
        continue
      let st : ProofState := { goals := #[{ context := { mfuncs := d.mfuncs, premises := #[] }, goal := d.type }] }
      proveLoop env n st
      match env.tryAddRule n d with
      | .ok env' => env := env'
      | .error _ => unreachable!
    | .ok _ _ => IO.eprintln "not implemented"
    | .error _ e => IO.eprintln s!"parse error: {e}"
