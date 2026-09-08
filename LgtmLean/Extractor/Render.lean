import Std
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

structure SExprEnv where
  /-- Functions that are defined globals.

  This is used to determine when a bare reference to a global needs to be rendered as a call instead of
  just as a reference to the global name. -/
  definedFunctions : Std.HashSet String

abbrev SExprM α := ReaderM SExprEnv α

def SExprM.run (functions : List LFunction) (s : SExprM α) : α :=
  let env := SExprEnv.mk (functions.foldr (λ f s => s.insert f.name) Std.HashSet.emptyWithCapacity)
  Id.run (ReaderT.run s env)

def LStructureDefinition.toSExpr (d : LStructureDefinition) : SExprM SExpr :=
  let fields := List.map (λ field => SExpr.list [SExpr.atom (toLispName field), SExpr.atom "nil", SExpr.atom ":read-only", SExpr.atom "t"]) d.fields
  pure (.block [.atom "cl-defstruct", .atom (toLgtmName d.name)] indentBy fields)

/-- Global names from Lean are namespaced, so translate appropriately -/
def translateGlobalName (name : String) : String :=
  toLgtmName (toLispName (name.map (λ c => if c == '.' then '-' else c)))

mutual

/-- Translate calls to Lean builtins and standard library functions into their elisp equivalents.

If the provided function is not a Lean builtin or standard library function, return none. -/
partial def translatePrimitives (fn : LExpr) (args : List LExpr) : SExprM (Option SExpr) :=
  match fn with
  | .global "instDecidableEqBool" => do
    let b₁ ← LExpr.toSExpr args[0]!
    let b₂ ← LExpr.toSExpr args[1]!
    pure (some (.list [.atom "eq", b₁, b₂]))
  | .global "Option.isSome" => do
    -- We represent none as nil in elisp, so the value is some if it is not nil
    let theValue ← LExpr.toSExpr args[0]!
    pure (some theValue)
  | .ctorRef "List.cons" => do
    let elt ← LExpr.toSExpr args[0]!
    let elts ← LExpr.toSExpr args[1]!
    pure (some (.list [.atom "cons", elt, elts]))
  | .global "List.isEmpty" => do
    let lst ← LExpr.toSExpr args[0]!
    pure (some (.list [.atom "seq-empty-p", lst]))
  | .global "List.all" => do
    let lst ← LExpr.toSExpr args[0]!
    let p ← LExpr.toSExpr args[1]!
    pure (some (.list [.atom "seq-every-p", p, lst]))
  | .global "List.map" => do
    let func ← LExpr.toSExpr args[0]!
    let lst ← LExpr.toSExpr args[1]!
    pure (some (.list [.atom "seq-map", func, lst]))
  | .global "List.flatten" => do
    let lst ← LExpr.toSExpr args[0]!
    pure (some (.list [.atom "seq-mapcat", .atom "#'identity", lst]))
  | .global "List.flatMap" => do
    let f ← LExpr.toSExpr args[0]!
    let lst ← LExpr.toSExpr args[1]!
    pure (some (.list [.atom "seq-mapcat", f, lst]))
  | .global "List.length" => do
    let lst ← LExpr.toSExpr args[0]!
    pure (some (.list [.atom "length", lst]))
  | .global "List.attach" => do
    -- This is a no-op in elisp because this only adds proof terms
    let l ← LExpr.toSExpr args[0]!
    pure (some l)
  | .global "String.isEmpty" => do
    let s ← LExpr.toSExpr args[0]!
    pure (some (.list [.atom "string-empty-p", s]))
  | .global "Std.HashMap.emptyWithCapacity" => pure (some (.list [.atom "make-hash-table"]))
  | .global "Std.HashMap.toList" => do
    let m ← LExpr.toSExpr args[2]!
    pure (some (.list [.atom "lgtm--hash-map-to-list", m]))
  | .global "Std.HashMap.map" => do
    let func ← LExpr.toSExpr args[2]!
    let map ← LExpr.toSExpr args[3]!
    pure (some (.list [.atom "lgtm--hash-map-map", func, map]))
  | .global "Std.HashMap.insert" => do
    let m ← LExpr.toSExpr args[2]!
    let key ← LExpr.toSExpr args[3]!
    let value ← LExpr.toSExpr args[4]!
    pure (some (.list [.atom "lgtm--hash-map-insert", key, value, m]))
  | .global "Std.HashMap.get" => do
    let m ← LExpr.toSExpr args[2]!
    let key ← LExpr.toSExpr args[3]!
    pure (some (.list [.atom "gethash", key, m]))
  | .global "Std.HashMap.size" => do
    let m ← LExpr.toSExpr args[2]!
    pure (some (.list [.atom "hash-table-count", m]))
  | .global "Prod.fst" => do
    let p ← LExpr.toSExpr args[0]!
    pure (some (.list [.atom "lgtm--pair-fst", p]))
  | .global "Prod.snd" => do
    let p ← LExpr.toSExpr args[0]!
    pure (some (.list [.atom "lgtm--pair-snd", p]))
  | .global "GetElem?.getElem!" => do
    -- WARNING/TODO: Is there an overload with lists here?
    let collection ← LExpr.toSExpr args[3]!
    let idx ← LExpr.toSExpr args[4]!
    pure (some (.list [.atom "gethash", idx, collection]))
  | .global "OfNat.ofNat" => do
    let i ← LExpr.toSExpr args[0]!
    pure (some i)
  | .global "Decidable.decide" => do
    -- These arise in the lifting of comparisons from Prop to Bool.  Since there is no Prop, we can just
    -- discard them in Lisp
    let t ← LExpr.toSExpr args[0]!
    pure (some t)
  | .global "Nat.decLe" => do
    let v₁ ← LExpr.toSExpr args[0]!
    let v₂ ← LExpr.toSExpr args[1]!
    pure (some (.list [.atom "<=", v₁, v₂]))
  | .global "Nat.decLt" => do
    let v₁ ← LExpr.toSExpr args[0]!
    let v₂ ← LExpr.toSExpr args[1]!
    pure (some (.list [.atom "<", v₁, v₂]))
  | _ => pure none

partial def LExpr.toSExpr (e : LExpr) : SExprM SExpr :=
  match e with
  | .var name => pure (SExpr.atom (toLispName name))
  | .global "Unit.unit" => pure (.atom "'unit")
  | .global "Prod.fst" => pure (.atom "#'lgtm--pair-fst")
  | .global "Prod.snd" => pure (.atom "#'lgtm--pair-snd")
  -- FIXME: Only add the hash prefix if the global definition is actually a function (not a constant)
  | .global name => pure (SExpr.atom ("#'" ++ translateGlobalName name))
  | .ctorRef "Option.none" => pure (SExpr.atom "nil")
  | .ctorRef "List.nil" => pure (SExpr.atom "nil")
  | .ctorRef "Bool.true" => pure (SExpr.atom "t")
  | .ctorRef "Bool.false" => pure (SExpr.atom "nil")
  | .ctorRef name =>
    -- Constructors in Lean have a `.mk` suffix. Drop that and replace with the equivalent prefix for cl-defstruct.
    pure (SExpr.atom ("#'make-" ++ toLgtmName (toLispName (name.dropEnd 3).toString)))
  | .lit (.nat n) => pure (.number n)
  | .lit (.str s) => pure (.string s)
  | .lam params body => do
    let sBody ← LExpr.toSExpr body
    pure (SExpr.block [.atom "lambda", .list (params.map (λ n => .atom (toLispName n)))] indentBy [sBody])
  | .app fn args => do match ← translatePrimitives fn args with
    | some translation => pure translation
    | none => do
      let sArgs ← args.mapM LExpr.toSExpr
      match fn with
      | .global name => do
        let sFunc := SExpr.atom (translateGlobalName name)
        pure (.list (sFunc :: sArgs))
      | .var name => do
        let sFunc := SExpr.atom (toLispName name)
        pure (.list (.atom "funcall" :: sFunc :: sArgs))
      | .ctorRef name => do
        -- Special case the rendering of these because they usually have many arguments
        let sFunc := SExpr.atom ("make-" ++ toLgtmName (toLispName (name.dropEnd 3).toString))
        pure (.block [sFunc] indentBy sArgs)
      | .lam _ _ => do
        let sFunc ← fn.toSExpr
        pure (.list (sFunc :: sArgs))
      | callee => pure (.list [.atom "error", .string s!"Unsupported callee {reprStr callee}"])
  | .letE name e body => do
    pure (.block [.atom "let", .list [.list [.atom (toLispName name), ← e.toSExpr]]] indentBy [← body.toSExpr])
  | .ite cond thenE elseE => do
    pure (.block [.atom "if", ← cond.toSExpr] indentBy [← thenE.toSExpr, ← elseE.toSExpr])
  -- `structName`'s `cl-defstruct` accessor for `fieldName` is named `<lgtm-struct-name>-<field-name>`,
  -- matching how `LStructureDefinition.render` names the struct and its slots.
  | .proj structName fieldName target => do
    pure (SExpr.list [SExpr.atom (toLgtmName structName ++ "-" ++ toLispName fieldName), ← target.toSExpr])
  -- FIXME: Not yet implemented -- pattern compilation needs a decided data representation for
  -- constructors first. Renders as a runtime error instead of `sorry` so the rest of the renderer
  -- stays evaluable/testable.
  | .matchE _ _ => pure (SExpr.list [SExpr.atom "error", SExpr.string "match expressions are not yet supported"])
  | .opaque reason => pure (SExpr.list [SExpr.atom "error", SExpr.string reason])

end

def LFunction.toSExpr (f : LFunction) : SExprM SExpr := do
  -- Names of Lgtm functions look like Lgtm.foo, so translate to Lgtm-foo so that the rest of the
  -- transformations turn them into a reasonable elisp name
  let name := translateGlobalName f.name
  let body ← f.body.toSExpr
  match f.parameters with
  | [] => pure (SExpr.block [SExpr.atom "defconst", SExpr.atom name] indentBy [body])
  | _ => do
    let arglist := SExpr.list (f.parameters.map (λ name => SExpr.atom (toLispName name)))
    let docstring := match f.docstring with
    | some ds => [SExpr.string ds]
    | none => []
    pure (SExpr.block [SExpr.atom "defun", SExpr.atom name, arglist] indentBy (docstring ++ [body]))

def testRender (s : SExprM SExpr) : String := SExpr.render (SExprM.run [] s)

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
#eval testRender (LStructureDefinition.toSExpr { name := "CommentRef", fields := ["id"] })

/-- info: "(cl-defstruct lgtm-tree\n  (value nil :read-only t)\n  (children nil :read-only t))" -/
#guard_msgs in
#eval testRender (LStructureDefinition.toSExpr { name := "Tree", fields := ["value", "children"] })

/-- info: "(cl-defstruct lgtm-modified-file-state\n)" -/
#guard_msgs in
#eval testRender (LStructureDefinition.toSExpr { name := "ModifiedFileState", fields := [] })

/-- info: "(cl-defstruct lgtm-comment-threads\n  (comment-tree-nodes nil :read-only t)\n  (server-comment-ids nil :read-only t)\n  (location-roots nil :read-only t))" -/
#guard_msgs in
#eval testRender (LStructureDefinition.toSExpr
  { name := "CommentThreads", fields := ["commentTreeNodes", "serverCommentIds", "locationRoots"] })

/-- info: "(defun lgtm-comment-is-persisted-to-server (c)\n  (lgtm-comment-backend-id c))" -/
#guard_msgs in
#eval testRender (LFunction.toSExpr
  { name := "Comment.isPersistedToServer",
    parameters := ["c"],
    body := LExpr.app (LExpr.global "Option.isSome") [LExpr.app (LExpr.global "Comment.backendId") [LExpr.var "c"]],
    docstring := none })

-- A `block` nested inside a `list` that's itself a body form of an outer `block` should still
-- have its own body forms indented cumulatively (outer `indent` + inner `indent`), not just the
-- inner block's own `indent` in isolation -- exercising `SExpr.renderIndent`'s threaded, rather
-- than purely local, indentation.
/-- info: "(defun\n  (foo (let\n    body1\n    body2)))" -/
#guard_msgs in
#eval SExpr.render (.block [.atom "defun"] 2
  [.list [.atom "foo", .block [.atom "let"] 2 [.atom "body1", .atom "body2"]]])
