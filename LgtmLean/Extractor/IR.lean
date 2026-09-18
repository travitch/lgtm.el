import Std

/-- An abstraction of Lean structure definitions.

Since the target language (lisp) is untyped, the types of the fields are erased.
The fields do not include Prop-typed entries. -/
public structure LStructureDefinition where
  name : String
  fields : List String
  isPublic : Bool := false
  deriving Repr

/-- An abstraction of Lean inductive definitions.

Each constructor is a pair of the constructor name and its arity.

In elisp, nullary constructors will be represented as symbols.  Other
constructors will be represented by unique cl-defstructs with the correct
number of fields. -/
public structure LInductiveDefinition where
  name : String
  constructors : List (String × Nat)
  deriving Repr

/-- A literal with a direct Lisp-representable form. -/
public inductive LLit where
  | nat (n : Nat) -- FIXME: Probably should be Int
  | str (s : String)
  | char (c : Char)
  deriving Repr, Inhabited, BEq

/-- A pattern that can occur on the left-hand side of a function clause or `match` alternative.

`fields` may themselves be `ctor` patterns to arbitrary depth: matching on a source-level
nested pattern (e.g. destructuring a field of a field in one alternative, as a tuple-of-tuples
pattern like `(t₁, t₂)` does) doesn't reliably compile into a separate auxiliary matcher call --
Lean sometimes inlines the whole nested `casesOn` tree into a single matcher's own body instead
-- so `tryDecodeMatcher` must be able to recover nesting of any depth from one such tree. -/
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

/-- Every top-level definition `e` refers to, in no particular order and possibly with repeats.

Only `global` references matter here: `ctorRef`s name data constructors and `proj`'s `structName`
names a structure, neither of which is a `LFunction` that could be emitted or dropped. -/
public partial def LExpr.globalRefs : LExpr → List String
  | .global name => [name]
  | .var _ | .ctorRef _ | .lit _ | .opaque _ => []
  | .lam _ body => body.globalRefs
  | .app fn args => fn.globalRefs ++ args.flatMap LExpr.globalRefs
  | .letE _ value body => value.globalRefs ++ body.globalRefs
  | .ite c t e => c.globalRefs ++ t.globalRefs ++ e.globalRefs
  | .proj _ _ target => target.globalRefs
  | .matchE discrs alts =>
    discrs.flatMap LExpr.globalRefs ++ alts.flatMap (fun (_, rhs) => rhs.globalRefs)

/-- A single `LgtmLean` function, translated to the simplified lambda calculus.

The extraction requires all function parameters to be named so we only have a representation
for argument lists.  The translation rejects the function definition form that is a list of
pattern bindings. -/
public structure LFunction where
  name : String
  parameters : List String
  body : LExpr
  docstring : Option String
  isPublic : Bool := false
  deriving Repr


structure Translations α [Hashable α] [BEq α] where
  functions : Std.HashMap α LFunction
  structures : Std.HashMap α LStructureDefinition
  inductives : Std.HashMap α LInductiveDefinition

def emptyTranslations : Translations String := ⟨Std.HashMap.emptyWithCapacity, Std.HashMap.emptyWithCapacity, Std.HashMap.emptyWithCapacity⟩
