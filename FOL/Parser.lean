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
  ASCII.alpha <|> char '_'

def idContinue : Parser Char :=
  ASCII.alphanum <|> char '_' <|> char '-'

def ident : Parser String :=
  (·.2.toString) <$> captureStr do
    let _ ← idStart
    dropMany idContinue

mutual

partial def term (depth := 0) (aux : HashMap String Nat) : Parser Term := do
  let id ← ident <* ws
  try
    let _ ← char '(' <* ws
    let args ← sepBy (char ',' <* ws) (term depth aux <* ws)
    return .func id args
  catch _ =>
    if let some idx := aux[id]? then
      return .bvar (idx - depth)
    else
      throwUnexpectedWithMessage none s!"unknown variable '{id}'"


partial def formula (depth := 0) (aux : HashMap String Nat) : Parser Term := do

  _


end
