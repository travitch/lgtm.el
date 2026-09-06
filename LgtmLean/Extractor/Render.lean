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

def LStructureDefinition.toSExpr (d : LStructureDefinition) : SExpr :=
  let fields := List.map (λ field => SExpr.list [SExpr.atom (toLispName field), SExpr.atom "nil", SExpr.atom ":read-only", SExpr.atom "t"]) d.fields
  .block [.atom "cl-defstruct", .atom (toLgtmName d.name)] indentBy fields

mutual

/-- Translate calls to Lean builtins and standard library functions into their elisp equivalents.

If the provided function is not a Lean builtin or standard library function, return none. -/
partial def translatePrimitives (fn : LExpr) (args : List LExpr) : Option SExpr :=
  match fn with
  | .global "Option.isSome" =>
    -- We represent none as nil in elisp, so the value is some if it is not nil
    some (args[0]!.toSExpr)
  | _ => none

partial def LExpr.toSExpr (e : LExpr) : SExpr :=
  match e with
  | .var name => SExpr.atom (toLispName name)
  | .global name => SExpr.atom (toLgtmName (toLispName name))
  | .ctorRef name => SExpr.atom (toLgtmName (toLispName name))
  | .lit (.nat n) => .number n
  | .lit (.str s) => .string s
  | .lam params body => .list [.atom "lambda", .list (params.map (λ n => .atom (toLispName n))), body.toSExpr]
  | .app fn args => match translatePrimitives fn args with
    | some translation => translation
    | none => .list (fn.toSExpr :: args.map LExpr.toSExpr)
  | .letE name e body => .block [.atom "let", .list [.list [.atom (toLispName name), e.toSExpr]]] indentBy [body.toSExpr]
  | .ite cond thenE elseE => .block [.atom "if", cond.toSExpr] indentBy [thenE.toSExpr, elseE.toSExpr]
  -- `structName`'s `cl-defstruct` accessor for `fieldName` is named `<lgtm-struct-name>-<field-name>`,
  -- matching how `LStructureDefinition.render` names the struct and its slots.
  | .proj structName fieldName target =>
    SExpr.list [SExpr.atom (toLgtmName structName ++ "-" ++ toLispName fieldName), target.toSExpr]
  -- FIXME: Not yet implemented -- pattern compilation needs a decided data representation for
  -- constructors first. Renders as a runtime error instead of `sorry` so the rest of the renderer
  -- stays evaluable/testable.
  | .matchE _ _ => SExpr.list [SExpr.atom "error", SExpr.string "match expressions are not yet supported"]
  | .opaque reason => SExpr.list [SExpr.atom "error", SExpr.string reason]

end

def LFunction.toSExpr (f : LFunction) : SExpr :=
  -- Names of Lgtm functions look like Lgtm.foo, so translate to Lgtm-foo so that the rest of the
  -- transformations turn them into a reasonable elisp name
  let name := f.name.map (λ c => if c == '.' then '-' else c)
  let body := f.body.toSExpr
  let arglist := SExpr.list (f.parameters.map (λ name => SExpr.atom (toLispName name)))
  SExpr.block [SExpr.atom "defun", SExpr.atom (toLgtmName (toLispName name)), arglist] indentBy [body]

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
#eval SExpr.render (LStructureDefinition.toSExpr { name := "CommentRef", fields := ["id"] })

/-- info: "(cl-defstruct lgtm-tree\n  (value nil :read-only t)\n  (children nil :read-only t))" -/
#guard_msgs in
#eval SExpr.render (LStructureDefinition.toSExpr { name := "Tree", fields := ["value", "children"] })

/-- info: "(cl-defstruct lgtm-modified-file-state\n)" -/
#guard_msgs in
#eval SExpr.render (LStructureDefinition.toSExpr { name := "ModifiedFileState", fields := [] })

/-- info: "(cl-defstruct lgtm-comment-threads\n  (comment-tree-nodes nil :read-only t)\n  (server-comment-ids nil :read-only t)\n  (location-roots nil :read-only t))" -/
#guard_msgs in
#eval SExpr.render (LStructureDefinition.toSExpr
  { name := "CommentThreads", fields := ["commentTreeNodes", "serverCommentIds", "locationRoots"] })

/-- info: "(defun lgtm-comment-is-persisted-to-server (c)\n  (lgtm-comment.backend-id c))" -/
#guard_msgs in
#eval SExpr.render (LFunction.toSExpr
  { name := "Comment.isPersistedToServer",
    parameters := ["c"],
    body := LExpr.app (LExpr.global "Option.isSome") [LExpr.app (LExpr.global "Comment.backendId") [LExpr.var "c"]] })
