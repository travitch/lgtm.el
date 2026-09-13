import Extractor.IR

inductive SExpr where
| number : Int → SExpr
/-- A quoted string literal -/
| string : String → SExpr
| atom : String → SExpr
/-- A Lisp application form -/
| list : List SExpr → SExpr
/-- A block introduced by a list of SExpr terms that indents by N spaces its body forms -/
| block : List SExpr → Nat → List SExpr → SExpr
deriving Inhabited

/-- Escape `s` for use inside an Emacs Lisp string literal -/
def escapeLispString (s : String) : String :=
  (s.replace "\\" "\\\\").replace "\"" "\\\""


/-- Render `s`, laying out every line at the absolute column `curIndent`, which accumulates as we
descend into nested `block`s (`curIndent + indent` for that block's own header/body) so indentation
compounds correctly regardless of nesting depth or what's structurally in between (a `block` nested
inside a `list` inside another `block` still lines up under its own header). -/
partial def SExpr.renderIndent (curIndent : Nat) (s : SExpr) : String :=
  match s with
  | .number n => toString n
  | .string s => "\"" ++ escapeLispString s ++ "\""
  | .atom s => s
  | .list xs => "(" ++ String.intercalate " " (xs.map (SExpr.renderIndent curIndent)) ++ ")"
  | .block header indent body =>
    let headerStr := String.intercalate " " (header.map (SExpr.renderIndent curIndent))
    let newIndent := curIndent + indent
    let indentStr := String.ofList (List.replicate newIndent ' ')
    let bodyStr := String.intercalate "\n" (body.map (fun e => indentStr ++ SExpr.renderIndent newIndent e))
    "(" ++ headerStr ++ "\n" ++ bodyStr ++ ")"

/-- Render an `SExpr` in the format used by emacs. -/
def SExpr.render (s : SExpr) : String := SExpr.renderIndent 0 s
