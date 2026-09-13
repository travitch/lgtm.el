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

/-- Render `c` using Emacs Lisp's basic character syntax, `?c` (see the "Basic Char Syntax" section
of the Elisp manual): a `?` immediately followed by the character, or by a backslash escape for the
handful of characters that need one to stay a single token. -/
def charToLispSyntax (c : Char) : String :=
  match c with
  | '\\' => "?\\\\"
  | '?' => "?\\?"
  | ' ' => "?\\s"
  | '\n' => "?\\n"
  | '\t' => "?\\t"
  | c => "?" ++ String.singleton c

/-- The direct Lisp representation of a literal, shared between rendering literal expressions and
literal patterns in `matchE`. -/
def LLit.toSExpr : LLit → SExpr
  | .nat n => .number n
  | .str s => .string s
  | .char c => .atom (charToLispSyntax c)

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

structure SExprEnv where
  /-- We keep the original translations around so we can determine which globals are functions vs
  those that are global constants.  We need to generate their names differently in elisp. -/
  translations : Translations String
  /-- The number of spaces to indent in block forms -/
  indentation : Nat
  /-- If a function is currently being translated, this holds its name -/
  currentFunction : Option String

structure SExprState where
  /-- Each constant has an entry in the map that is the set of other constants it depends on -/
  calledGlobalNames : Std.HashMap String (Std.HashSet String)

def emptyState : SExprState := ⟨Std.HashMap.emptyWithCapacity⟩

abbrev SExprM α := StateT SExprState (ReaderM SExprEnv) α

def insertOrSingleton (s : String) (elts : Option (Std.HashSet String)) : Option (Std.HashSet String) :=
  match elts with
  | none => some (Std.HashSet.emptyWithCapacity.insert s)
  | some set => some (set.insert s)

/-- Record that `name` has been used by the function definition currently being translated. -/
def recordUsedNameInContext (name : String) : SExprM Unit := do
  match (← read).currentFunction with
  | none => pure ()
  | some currentFuncName => do
    modifyGet (fun s => ((), { s with calledGlobalNames := s.calledGlobalNames.alter currentFuncName (insertOrSingleton name) }))

/-- If the given name refers to an inductive constructor, return true. -/
def isInductiveConstructor (name : String) : SExprM Bool := do
  let env ← read
  match (name.split '.').toList with
  | [typeName, _conName] => match env.translations.inductives[typeName.toString]? with
    | some _ => pure true
    | none => pure false
  | _ => pure false

def indentBy : SExprM Nat := do pure (← read).indentation

def SExprM.run (indentation : Nat) (translations : Translations String) (s : SExprM α) : α × SExprState :=
  let env := SExprEnv.mk translations indentation none
  Id.run (ReaderT.run (StateT.run s emptyState) env)

def LStructureDefinition.toSExpr (d : LStructureDefinition) : SExprM SExpr := do
  let fields := List.map (λ field => SExpr.list [SExpr.atom (toLispName field), SExpr.atom "nil", SExpr.atom ":read-only", SExpr.atom "t"]) d.fields
  pure (.block [.atom "cl-defstruct", .atom (toLgtmName d.name)] (← indentBy) fields)

/-- Global names from Lean are namespaced, so translate appropriately -/
def translateGlobalName (name : String) : String :=
  toLgtmName (toLispName (name.map (λ c => if c == '.' then '-' else c)))

/-- The elisp symbol naming constructor `name` (fully-qualified, e.g. `ThreadLocation.topLevel`):
the literal value of a nullary constructor, and the tag in position 0 of a non-nullary
constructor's vector. See [ref:inductive-type-representation]. -/
def translateConstructorTag (name : String) : String :=
  toLispName (name.map (λ c => if c == '.' then '-' else c))

/-- Render `p` as a `pcase` "backquote pattern" fragment (the `QPAT` grammar), suitable for
splicing directly inside a backquote pattern. Variables and wildcards need an explicit `,` to turn
them into sub-patterns (`UPAT`s); nullary-constructor symbols and literals already match themselves
via `equal`; constructors with fields become vector patterns. See
[ref:inductive-type-representation]. -/
partial def LPat.toQPat : LPat → String
  | .var name => "," ++ toLispName name
  | .wildcard => ",_"
  | .lit l => SExpr.render l.toSExpr
  -- `Option.none`/`Option.some` are special-cased to `nil`/the bare value, and `Bool.true`/
  -- `Bool.false` to `t`/`nil`, rather than the usual symbol/vector encoding. See
  -- [ref:inductive-type-representation].
  | .ctor "Option.none" [] => "nil"
  | .ctor "Option.some" [p] => p.toQPat
  | .ctor "Bool.true" [] => "t"
  | .ctor "Bool.false" [] => "nil"
  | .ctor name [] => translateConstructorTag name
  | .ctor name fields =>
    "[" ++ String.intercalate " " (translateConstructorTag name :: fields.map LPat.toQPat) ++ "]"

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
  | .ctorRef "Option.some" => do
    let v ← LExpr.toSExpr args[0]!
    pure (some v)
  | .ctorRef "Except.ok" => do
    let v ← LExpr.toSExpr args[0]!
    pure (some (.list [.atom "vector", .atom "'except-ok", v]))
  | .ctorRef "Except.error" => do
    let v ← LExpr.toSExpr args[0]!
    pure (some (.list [.atom "vector", .atom "'except-error", v]))
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
  | .global "List.idxOf" => do
    let elt ← LExpr.toSExpr args[0]!
    let lst ← LExpr.toSExpr args[1]!
    pure (some (.list [.atom "lgtm--list-idx-of", elt, lst]))
  | .global "List.findIdx?" => do
    let p ← LExpr.toSExpr args[0]!
    let lst ← LExpr.toSExpr args[1]!
    pure (some (.list [.atom "lgtm--list-find-idx", p, lst]))
  | .global "List.mergeSort" => do
    let seq ← LExpr.toSExpr args[0]!
    let comparator ← LExpr.toSExpr args[1]!
    pure (some (.list [.atom "seq-sort", comparator, seq]))
  | .global "String.isEmpty" => do
    let s ← LExpr.toSExpr args[0]!
    pure (some (.list [.atom "string-empty-p", s]))
  | .global "Std.HashMap.emptyWithCapacity" => pure (some (.list [.atom "make-hash-table"]))
  | .global "Std.HashMap.toList" => do
    let m ← LExpr.toSExpr args[0]!
    pure (some (.list [.atom "lgtm--hash-map-to-list", m]))
  | .global "Std.HashMap.map" => do
    let func ← LExpr.toSExpr args[0]!
    let map ← LExpr.toSExpr args[1]!
    pure (some (.list [.atom "lgtm--hash-map-map", func, map]))
  | .global "Std.HashMap.insert" => do
    let m ← LExpr.toSExpr args[0]!
    let key ← LExpr.toSExpr args[1]!
    let value ← LExpr.toSExpr args[2]!
    pure (some (.list [.atom "lgtm--hash-map-insert", key, value, m]))
  | .global "Std.HashMap.get" => do
    let m ← LExpr.toSExpr args[0]!
    let key ← LExpr.toSExpr args[1]!
    pure (some (.list [.atom "gethash", key, m]))
  | .global "Std.HashMap.size" => do
    let m ← LExpr.toSExpr args[0]!
    pure (some (.list [.atom "hash-table-count", m]))
  | .global "Prod.fst" => do
    let p ← LExpr.toSExpr args[0]!
    pure (some (.list [.atom "lgtm--pair-fst", p]))
  | .global "Prod.snd" => do
    let p ← LExpr.toSExpr args[0]!
    pure (some (.list [.atom "lgtm--pair-snd", p]))
  | .global "GetElem?.getElem!" => do
    -- WARNING/TODO: Is there an overload with lists here?
    let collection ← LExpr.toSExpr args[1]!
    let idx ← LExpr.toSExpr args[2]!
    pure (some (.list [.atom "gethash", idx, collection]))
  | .global "GetElem.getElem" => do
    let collection ← LExpr.toSExpr args[1]!
    let idx ← LExpr.toSExpr args[2]!
    pure (some (.list [.atom "seq-elt", collection, idx]))
  | .global "GetElem?.getElem?" => do
    let collection ← LExpr.toSExpr args[1]!
    let idx ← LExpr.toSExpr args[2]!
    pure (some (.list [.atom "seq-elt", collection, idx]))
  | .global "Nat.min" => do
    let lhs ← LExpr.toSExpr args[0]!
    let rhs ← LExpr.toSExpr args[1]!
    pure (some (.list [.atom "min", lhs, rhs]))
  | .global "Min.min" => do
    let lhs ← LExpr.toSExpr args[0]!
    let rhs ← LExpr.toSExpr args[1]!
    pure (some (.list [.atom "min", lhs, rhs]))
  | .global "Max.max" => do
    let lhs ← LExpr.toSExpr args[0]!
    let rhs ← LExpr.toSExpr args[1]!
    pure (some (.list [.atom "max", lhs, rhs]))
  | .global "HAdd.hAdd" => do
    let lhs ← LExpr.toSExpr args[0]!
    let rhs ← LExpr.toSExpr args[1]!
    pure (some (.list [.atom "+", lhs, rhs]))
  | .global "HSub.hSub" => do
    let lhs ← LExpr.toSExpr args[0]!
    let rhs ← LExpr.toSExpr args[1]!
    pure (some (.list [.atom "-", lhs, rhs]))
  | .global "Subtype.val" => do
    -- Since we ignore the proof component of Subtype values, we just represent them with the bare variable
    -- so we pass it through.
    let v ← LExpr.toSExpr args[1]!
    pure (some v)
  | .ctorRef "Prod.mk" => do
    let fst ← LExpr.toSExpr args[0]!
    let snd ← LExpr.toSExpr args[1]!
    pure (some (.list [.atom "vector", fst, snd]))
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
  | .global "BEq.beq" => do
    let v₁ ← LExpr.toSExpr args[0]!
    let v₂ ← LExpr.toSExpr args[1]!
    pure (some (.list [.atom "equal", v₁, v₂]))
  | _ => pure none

partial def LExpr.toSExpr (e : LExpr) : SExprM SExpr :=
  match e with
  | .var name => pure (SExpr.atom (toLispName name))
  | .global "Unit.unit" => pure (.atom "'unit")
  | .global "Prod.fst" => pure (.atom "#'lgtm--pair-fst")
  | .global "Prod.snd" => pure (.atom "#'lgtm--pair-snd")
  | .global name => do
    recordUsedNameInContext name
    match (← read).translations.functions[name]? with
    | some lfunc => match lfunc.parameters with
      | [] => pure (SExpr.atom (translateGlobalName name))
      | _ => pure (SExpr.atom ("#'" ++ translateGlobalName name))
    | none => pure (SExpr.atom ("#'" ++ translateGlobalName name))
  | .ctorRef "Option.none" => pure (SExpr.atom "nil")
  | .ctorRef "List.nil" => pure (SExpr.atom "nil")
  | .ctorRef "Bool.true" => pure (SExpr.atom "t")
  | .ctorRef "Bool.false" => pure (SExpr.atom "nil")
  | .ctorRef name => do
    match ← isInductiveConstructor name with
    | false =>
      -- Constructors in Lean have a `.mk` suffix. Drop that and replace with the equivalent prefix for cl-defstruct.
      pure (SExpr.atom ("#'make-" ++ toLgtmName (toLispName (name.dropEnd 3).toString)))
    | true => pure (SExpr.atom ("'" ++ translateGlobalName name))
  | .lit l => pure l.toSExpr
  | .lam params body => do
    let sBody ← LExpr.toSExpr body
    pure (SExpr.block [.atom "lambda", .list (params.map (λ n => .atom (toLispName n)))] (← indentBy) [sBody])
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
        if ← isInductiveConstructor name then
          let sFunc := SExpr.atom "vector"
          let tag := SExpr.atom ("'" ++ translateGlobalName name)
          pure (.block [sFunc] (← indentBy) (tag :: sArgs))
        else do
          -- Special case the rendering of these because they usually have many arguments
          let sFunc := SExpr.atom ("make-" ++ toLgtmName (toLispName (name.dropEnd 3).toString))
          pure (.block [sFunc] (← indentBy) sArgs)
      | .lam _ _ => do
        let sFunc ← fn.toSExpr
        pure (.list (sFunc :: sArgs))
      | .proj .. => do
        -- The struct-field accessor call itself evaluates to a function value (see the
        -- `Extractor.lean` `translateApp` comment on projection-typed fields), so, like a `.var`
        -- head, it needs `funcall` rather than being spliced directly into the call position.
        let sFunc ← fn.toSExpr
        pure (.list (.atom "funcall" :: sFunc :: sArgs))
      | callee => pure (.list [.atom "error", .string s!"Unsupported callee {reprStr callee}"])
  | .letE name e body => do
    pure (.block [.atom "let", .list [.list [.atom (toLispName name), ← e.toSExpr]]] (← indentBy) [← body.toSExpr])
  | .ite cond thenE elseE => do
    pure (.block [.atom "if", ← cond.toSExpr] (← indentBy) [← thenE.toSExpr, ← elseE.toSExpr])
  -- `structName`'s `cl-defstruct` accessor for `fieldName` is named `<lgtm-struct-name>-<field-name>`,
  -- matching how `LStructureDefinition.render` names the struct and its slots.
  | .proj structName fieldName target => do
    pure (SExpr.list [SExpr.atom (toLgtmName structName ++ "-" ++ toLispName fieldName), ← target.toSExpr])
  | .matchE discrs alts => do
    let sDiscrs ← discrs.mapM LExpr.toSExpr
    let sAlts ← alts.mapM (λ (pats, body) => do
      let sBody ← body.toSExpr
      let patText := match pats with
        | [p] => "`" ++ p.toQPat
        | ps => "`(" ++ String.intercalate " " (ps.map LPat.toQPat) ++ ")"
      pure (SExpr.list [SExpr.atom patText, sBody]))
    -- `pcase` dispatches on a single value, so multiple discriminants are bundled into a list
    -- that each alternative's pattern then destructures. See [ref:inductive-type-representation].
    match sDiscrs with
    | [d] => pure (SExpr.block [SExpr.atom "pcase", d] (← indentBy) sAlts)
    | ds => pure (SExpr.block [SExpr.atom "pcase", SExpr.list (SExpr.atom "list" :: ds)] (← indentBy) sAlts)
  | .opaque reason => pure (SExpr.list [SExpr.atom "error", SExpr.string reason])

end

def LFunction.toSExpr (f : LFunction) : SExprM SExpr := withReader (fun e => if f.parameters.isEmpty then { e with currentFunction := some f.name } else e) do
  -- Names of Lgtm functions look like Lgtm.foo, so translate to Lgtm-foo so that the rest of the
  -- transformations turn them into a reasonable elisp name
  let name := translateGlobalName f.name
  let body ← f.body.toSExpr
  match f.parameters with
  | [] => pure (SExpr.block [SExpr.atom "defconst", SExpr.atom name] (← indentBy) [body])
  | _ => do
    let arglist := SExpr.list (f.parameters.map (λ name => SExpr.atom (toLispName name)))
    let docstring := match f.docstring with
    | some ds => [SExpr.string ds.trimAscii.toString]
    | none => []
    pure (SExpr.block [SExpr.atom "defun", SExpr.atom name, arglist] (← indentBy) (docstring ++ [body]))

def testRender (s : SExprM SExpr) : String := SExpr.render (SExprM.run 2 emptyTranslations s).1

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

-- A global nullary function (a "global constant", translated to a `defconst` by
-- `LFunction.toSExpr`) is referenced by its bare elisp name, not prefixed with `#'` like ordinary
-- function references: a `defconst` symbol's value is read directly, whereas calling a function
-- via `funcall`/`apply` needs a sharp-quoted function reference.
/-- info: "(defun lgtm-uses-constant (x)\n  lgtm-some-constant)" -/
#guard_msgs in
#eval
  let translations : Translations String :=
    { emptyTranslations with
      functions := Std.HashMap.emptyWithCapacity.insert "someConstant"
        { name := "someConstant", parameters := [], body := .lit (.nat 0), docstring := none } }
  SExpr.render (SExprM.run 2 translations (LFunction.toSExpr
    { name := "usesConstant", parameters := ["x"], body := .global "someConstant", docstring := none })).1

-- A bare reference to a nullary inductive constructor (per `LExpr.ctorRef`'s doc comment, a
-- constructor is used bare, with no `app` wrapper, when it takes no arguments) renders as a quoted
-- elisp symbol, matching how nullary constructors are represented per
-- [ref:inductive-type-representation] -- unlike a `.mk`-suffixed structure constructor, which
-- renders as a `make-` function reference instead.
/-- info: "'lgtm-thread-location-top-level" -/
#guard_msgs in
#eval
  let translations : Translations String :=
    { emptyTranslations with
      inductives := Std.HashMap.emptyWithCapacity.insert "ThreadLocation"
        { name := "ThreadLocation", constructors := [("ThreadLocation.topLevel", 0), ("ThreadLocation.nested", 1)] } }
  SExpr.render (SExprM.run 2 translations (LExpr.toSExpr (.ctorRef "ThreadLocation.topLevel"))).1

-- An inductive constructor applied to arguments renders as a `vector` form with the quoted
-- constructor symbol in position 0 followed by the field values, per
-- [ref:inductive-type-representation] -- unlike a `.mk`-suffixed structure constructor applied to
-- arguments, which renders as a `make-` function call instead.
/-- info: "(vector\n  'lgtm-thread-location-nested\n  parent)" -/
#guard_msgs in
#eval
  let translations : Translations String :=
    { emptyTranslations with
      inductives := Std.HashMap.emptyWithCapacity.insert "ThreadLocation"
        { name := "ThreadLocation", constructors := [("ThreadLocation.topLevel", 0), ("ThreadLocation.nested", 1)] } }
  SExpr.render (SExprM.run 2 translations
    (LExpr.toSExpr (.app (.ctorRef "ThreadLocation.nested") [.var "parent"]))).1

-- `Except.ok`/`Except.error` are special-cased in `translatePrimitives` to render as a two-element
-- `vector` tagged with a plain (unnamespaced) quoted symbol, rather than going through the general
-- inductive-constructor encoding (which would require registering an `Except` `LInductiveDefinition`
-- and would namespace the tag as `'lgtm-except-ok`).
/-- info: "(vector 'except-ok 42)" -/
#guard_msgs in
#eval testRender (LExpr.toSExpr (.app (.ctorRef "Except.ok") [.lit (.nat 42)]))

/-- info: "(vector 'except-error \"oops\")" -/
#guard_msgs in
#eval testRender (LExpr.toSExpr (.app (.ctorRef "Except.error") [.lit (.str "oops")]))

-- `matchE` over a single discriminant: a nullary constructor becomes a bare symbol pattern, and a
-- constructor with a field becomes a vector pattern with the field bound via `,`.
/-- info: "(pcase loc\n  (`thread-location-top-level \"top\")\n  (`[thread-location-nested ,parent] parent))" -/
#guard_msgs in
#eval testRender (LExpr.toSExpr
  (.matchE [.var "loc"]
    [([.ctor "ThreadLocation.topLevel" []], .lit (.str "top")),
     ([.ctor "ThreadLocation.nested" [.var "parent"]], .var "parent")]))

-- `matchE` over multiple discriminants: the discriminants are bundled into a `list`, and each
-- alternative matches a backquoted list pattern against it.
/-- info: "(pcase (list a b)\n  (`(,x ,_) x))" -/
#guard_msgs in
#eval testRender (LExpr.toSExpr
  (.matchE [.var "a", .var "b"] [([.var "x", .wildcard], .var "x")]))

-- Literal patterns match themselves via `equal`; a trailing wildcard alternative catches the rest.
/-- info: "(pcase s\n  (`\"foo\" \"yes\")\n  (`,_ \"no\"))" -/
#guard_msgs in
#eval testRender (LExpr.toSExpr
  (.matchE [.var "s"]
    [([.lit (.str "foo")], .lit (.str "yes")),
     ([.wildcard], .lit (.str "no"))]))

-- `Option.none`/`Option.some` patterns are special-cased to match their `nil`/unwrapped-value
-- representation instead of the usual symbol/vector encoding.
/-- info: "(pcase o\n  (`nil \"none\")\n  (`,x x))" -/
#guard_msgs in
#eval testRender (LExpr.toSExpr
  (.matchE [.var "o"]
    [([.ctor "Option.none" []], .lit (.str "none")),
     ([.ctor "Option.some" [.var "x"]], .var "x")]))

-- `Bool.true`/`Bool.false` patterns are special-cased to match their `t`/`nil` representation
-- instead of the usual symbol encoding.
/-- info: "(pcase b\n  (`t \"yes\")\n  (`nil \"no\"))" -/
#guard_msgs in
#eval testRender (LExpr.toSExpr
  (.matchE [.var "b"]
    [([.ctor "Bool.true" []], .lit (.str "yes")),
     ([.ctor "Bool.false" []], .lit (.str "no"))]))

-- A `block` nested inside a `list` that's itself a body form of an outer `block` should still
-- have its own body forms indented cumulatively (outer `indent` + inner `indent`), not just the
-- inner block's own `indent` in isolation -- exercising `SExpr.renderIndent`'s threaded, rather
-- than purely local, indentation.
/-- info: "(defun\n  (foo (let\n    body1\n    body2)))" -/
#guard_msgs in
#eval SExpr.render (.block [.atom "defun"] 2
  [.list [.atom "foo", .block [.atom "let"] 2 [.atom "body1", .atom "body2"]]])



/- [tag:inductive-type-representation]

There are no types in elisp equivalent to Lean inductive definitions.  We represent them in elisp as follows:

- Nullary constructors are represented as symbols.  A constructor like `ThreadLocation.topLevel` becomes an elisp symbol `'thread-location-top-level`
- Other constructors are represented as vectors where the first element is a symbol with the name of the corresponding constructor and the other elements are the values in the inductive constructor

Match expressions over inductives are implemented using elisp's `pcase` macro.

This uniform representation means that no special type declarations are required for inductives.

As special cases:
- Implement Lean's `Option.none` as standard elisp `nil` and `Option.some x` as `x` (i.e., just the value itself)
- Implement Lean's `Bool.true` and `Bool.false` as elisp `t` and `nil`, respectively

-/
