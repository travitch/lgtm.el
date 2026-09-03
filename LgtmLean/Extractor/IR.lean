/-- An abstraction of Lean structure definitions.

Since the target language (lisp) is untyped, the types of the fields are erased.
The fields do not include Prop-typed entries. -/
public structure LStructureDefinition where
  name : String
  fields : List String
  deriving Repr

/-- A literal with a direct Lisp-representable form. -/
public inductive LLit where
  | nat (n : Nat)
  | str (s : String)
  deriving Repr, Inhabited, BEq

/-- A pattern that can occur on the left-hand side of a function clause or `match` alternative.

Only a single level of constructor nesting is modeled: `fields` are always variables or
wildcards, never nested `ctor` patterns. This matches every pattern actually written in
`LgtmLean` (which are all shallow); a deeper source pattern is instead compiled by Lean into a
*nested* matcher application, which shows up as ordinary control flow in the body of the
enclosing alternative rather than as a nested `LPat`. -/
public inductive LPat where
  | var (name : String)
  | wildcard
  | lit (l : LLit)
  | ctor (name : String) (fields : List LPat)
  deriving Repr, Inhabited

/-- The simplified lambda calculus that `LgtmLean` function bodies are translated into.

All `Prop`-sorted (proof) and `Sort`-sorted (type) subterms have already been erased by
translation time: they carry no run-time representation, so a Lisp target has nothing to receive
them. -/
public inductive LExpr where
  /-- A reference to a locally bound variable (a function parameter, `let`, or pattern-bound
  name). -/
  | var (name : String)
  /-- A reference to another top-level definition. -/
  | global (name : String)
  /-- A reference to a data constructor, used bare (arity 0) or as the head of `app`. -/
  | ctorRef (name : String)
  | lit (l : LLit)
  | lam (params : List String) (body : LExpr)
  | app (fn : LExpr) (args : List LExpr)
  | letE (name : String) (value : LExpr) (body : LExpr)
  | ite (cond thenE elseE : LExpr)
  | proj (structName : String) (fieldName : String) (target : LExpr)
  /-- A (possibly multi-way) pattern match: one pattern per discriminant, per alternative. -/
  | matchE (discrs : List LExpr) (alts : List (List LPat × LExpr))
  /-- A subterm that couldn't be translated (an axiom/`sorry`, or an unrecognized `Expr` shape).
  Keeps a single bad declaration from taking down the whole extraction run. -/
  | opaque (reason : String)
  deriving Repr, Inhabited

/-- A single `LgtmLean` function, translated to the simplified lambda calculus.

The extraction requires all function parameters to be named so we only have a representation
for argument lists.  The translation rejects the function definition form that is a list of
pattern bindings. -/
public structure LFunction where
  name : String
  parameters : List String
  body : LExpr
  deriving Repr
