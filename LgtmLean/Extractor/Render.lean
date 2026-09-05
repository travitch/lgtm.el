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

/-- Escape `s` for use inside an Emacs Lisp string literal -/
def escapeLispString (s : String) : String :=
  (s.replace "\\" "\\\\").replace "\"" "\\\""

/-- Render an `SExpr` in the format used by emacs. -/
partial def SExpr.render (s : SExpr) : String :=
  match s with
  | .number n => toString n
  | .string s => "\"" ++ escapeLispString s ++ "\""
  | .atom s => s
  | .list xs => "(" ++ String.intercalate " " (xs.map SExpr.render) ++ ")"
  | .block header indent body =>
    let headerStr := String.intercalate " " (header.map SExpr.render)
    let indentStr := String.ofList (List.replicate indent ' ')
    let indentLines (s : String) : String :=
      String.intercalate "\n" ((s.splitOn "\n").map (indentStr ++ ·))
    let bodyStr := String.intercalate "\n" (body.map (fun e => indentLines (SExpr.render e)))
    "(" ++ headerStr ++ "\n" ++ bodyStr ++ ")"

/-- Convert names from camel or pascal case to kebab case. -/
def toLispName (s : String) : String :=
  let cs := s.toList.toArray
  let n := cs.size
  let isSep (c : Char) : Bool := c == '_' || c == ' ' || c == '-'
  let hyphenated : List Char := Id.run do
    let mut acc : List Char := []
    for i in [0:n] do
      let c := cs[i]!
      if isSep c then
        acc := '-' :: acc
      else if c.isUpper then
        let prev? := if i == 0 then none else some cs[i - 1]!
        let nextIsLower := i + 1 < n && (cs[i + 1]!).isLower
        let boundary := match prev? with
          | none => false
          | some p => p.isLower || p.isDigit || (p.isUpper && nextIsLower)
        if boundary then
          acc := '-' :: acc
        acc := c.toLower :: acc
      else
        acc := c :: acc
    pure acc.reverse
  String.intercalate "-" ((String.ofList hyphenated).splitOn "-" |>.filter (· ≠ ""))


def toLgtmName (s : String) : String := "lgtm-" ++ toLispName s

def indentBy : Nat := 2

def LStructureDefinition.render (d : LStructureDefinition) : String :=
  let fields := List.map (λ field => SExpr.list [SExpr.atom (toLispName field), SExpr.atom "nil", SExpr.atom ":read-only", SExpr.atom "t"]) d.fields
  let sexpr := .block [.atom "cl-defstruct", .atom (toLgtmName d.name)] indentBy fields
  SExpr.render sexpr


/-- info: "comment-threads" -/
#guard_msgs in
#eval toLispName "CommentThreads"

/-- info: "backend-id" -/
#guard_msgs in
#eval toLispName "backendId"

/-- info: "parse-url-path" -/
#guard_msgs in
#eval toLispName "parseURLPath"

/-- info: "start-line" -/
#guard_msgs in
#eval toLispName "startLine"

/-- info: "server-id" -/
#guard_msgs in
#eval toLispName "ServerId"

/-- info: "loc-2" -/
#guard_msgs in
#eval toLispName "loc_2"

/-- info: "h-selected-comment-well-formed" -/
#guard_msgs in
#eval toLispName "hSelectedCommentWellFormed"

/-- info: "is-top-level" -/
#guard_msgs in
#eval toLispName "isTopLevel"

/-- info: "modified-file-state" -/
#guard_msgs in
#eval toLispName "ModifiedFileState"

/-- info: "sha256-hash" -/
#guard_msgs in
#eval toLispName "sha256Hash"

/-- info: "s" -/
#guard_msgs in
#eval toLispName "s"

/-- info: "comment-tree-bootstrap-state" -/
#guard_msgs in
#eval toLispName "CommentTreeBootstrapState"

/-- info: "weird-name" -/
#guard_msgs in
#eval toLispName "__weird__Name__"

/-- info: "(cl-defstruct lgtm-comment-ref\n  (id nil :read-only t))" -/
#guard_msgs in
#eval LStructureDefinition.render { name := "CommentRef", fields := ["id"] }

/-- info: "(cl-defstruct lgtm-tree\n  (value nil :read-only t)\n  (children nil :read-only t))" -/
#guard_msgs in
#eval LStructureDefinition.render { name := "Tree", fields := ["value", "children"] }

/-- info: "(cl-defstruct lgtm-modified-file-state\n)" -/
#guard_msgs in
#eval LStructureDefinition.render { name := "ModifiedFileState", fields := [] }

/-- info: "(cl-defstruct lgtm-comment-threads\n  (comment-tree-nodes nil :read-only t)\n  (server-comment-ids nil :read-only t)\n  (location-roots nil :read-only t))" -/
#guard_msgs in
#eval LStructureDefinition.render
  { name := "CommentThreads", fields := ["commentTreeNodes", "serverCommentIds", "locationRoots"] }
