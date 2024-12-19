import FOL.Basic
import Parser

open Std Parser Char

namespace FOL.Parser

abbrev Parser := SimpleParser Substring Char

def ws : Parser Unit := do
  dropMany Unicode.whitespace

def ws1 : Parser Unit := do
  dropMany1 Unicode.whitespace

def idStart : Parser Char :=
  Unicode.alpha <|> char '_'

def idContinue : Parser Char :=
  Unicode.alpha <|> (tokenFilter isDigit) <|> char '_'

def ident : Parser String :=
  (·.2.toString) <$> captureStr do
    let _ ← idStart
    dropMany idContinue

def nat : Parser Nat := do
  let some res ←
    (·.2.toString.toNat?) <$> captureStr do
      dropMany ASCII.numeric
    | throwUnexpectedWithMessage (msg := "nat expected")
  return res

partial def term (depth := 0) (aux : HashMap String Nat := {}) : Parser Term := do
  match ← peek with
  | '@' =>
    let _ ← char '@'
    let id ← ident
    let args ← option? <| char '(' *> ws *> sepBy (char ',' <* ws) (term depth aux <* ws) <* ws <* char ')'
    let args := args.getD #[]
    return .mfunc id.toName args
  | '\\' =>
    let _ ← char '\\' <* ws
    let id ← ident <* ws
    let varId ← ident <* ws
    let _ ← char ',' <* ws
    let body ← term (depth + 1) (aux.insert varId depth)
    return .binder id.toName body
  | _ =>
    let id ← ident
    if let some varDepth := aux[id]? then
      return .bvar (depth - (varDepth + 1))
    else
      let args ← option? <| char '(' *> ws *> sepBy (char ',' <* ws) (term depth aux <* ws) <* ws <* char ')'
      let args := args.getD #[]
      return .func id.toName args

def parseTerm : Parser Term := do
  term <* ws <* endOfInput

partial def ruleType : Parser RuleType := do
  ws
  match ← peek with
  | '(' =>
    let _ ← char '(' <* ws
    let p ← ruleType <* ws
    let _ ← chars "|-" <* ws
    let c ← ruleType <* ws
    let _ ← char ')' <* ws
    return .node p c
  | _ =>
    let t ← term
    return .leaf t

def parseRuleType : Parser RuleType := do
  ruleType <* ws <* endOfInput

def funcData : Parser FuncData := do
  let arr ← sepBy1 (chars "->" <* ws) (ident <* ws)
  return { argSorts := arr.pop.map (·.toName), resSort := arr.back!.toName }
