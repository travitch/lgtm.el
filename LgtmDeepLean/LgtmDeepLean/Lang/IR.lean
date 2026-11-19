module

public inductive Ty where
  | bool
  | int
  | string
  | option : Ty → Ty
  /-- A value of the second type, or an error of the first: Lean's own `Except`, read in the order
`Except ε α` relates them — the error type first and the payload second.

Like `option` and unlike `struct` and `inductive` it carries the types it relates rather than naming
a declaration, so there is nothing to declare and nothing for `TypeDecls` to resolve, and two except
types are the same when both halves are.

Where an option says whether there is a value, this says what there is *instead* of one: an error
carries a value of its own, which is the whole of what separates the two type formers. -/
  | except : Ty → Ty → Ty
  | list : Ty → Ty
  | hashmap : Ty → Ty → Ty
  /-- A fixed-length sequence of values, each at the type its position gives it: `tuple [int, string]`
is an `int` beside a `string`.

Positional and structural — it names no declaration, the way `list` and `option` name none — so it
is to a struct what an inductive constructor's data is to a struct's fields: there is nothing to
declare and nothing for `TypeDecls` to resolve, and two tuple types are the same when they are the
same types in the same order.

Unlike `list` it is heterogeneous and its length is part of its type, which is what makes it the type
of *one binding* of a hashmap: `tuple [kt, vt]` is what `Expression.hashmapToList` produces a list
of. -/
  | tuple : List Ty → Ty
  /-- A function from the types of its parameters to the type of its result. -/
  | fn : List Ty → Ty → Ty
  /-- A declared structure type (matched nominally). -/
  | struct : String → Ty
  /-- A declared inductive type (matched nominally). -/
  | ind : String → Ty
  deriving Repr

public abbrev FieldName :=
  String

/-- A structure type declaration with named and typed fields.

Field names must be unique (see `StructDecl.FieldNamesUnique` [ref:struct_field_names_unique]). -/
public structure StructDecl where
  name : String
  fields : List (FieldName × Ty)
  deriving Repr

public abbrev CtorName :=
  String

/-- A declaration of an inductive type that is similar to Lean's built-in inductives.

Inductive constructor names are required to be unique (`InductiveDecl.CtorNamesUnique`
[ref:inductive_constructor_names_unique]).  Constructor names may be reused across unrelated
inductives. -/
public structure InductiveDecl where
  name : String
  constructors : List (CtorName × List Ty)
  deriving Repr

mutual
@[expose] public def Ty.beq : Ty → Ty → Bool
  | .bool, .bool => true
  | .int, .int => true
  | .string, .string => true
  | .option a, .option b => Ty.beq a b
  | .except e1 a1, .except e2 a2 => Ty.beq e1 e2 && Ty.beq a1 a2
  | .list a, .list b => Ty.beq a b
  | .hashmap k1 v1, .hashmap k2 v2 => Ty.beq k1 k2 && Ty.beq v1 v2
  | .tuple as, .tuple bs => Ty.beqList as bs
  | .fn as r, .fn bs r' => Ty.beqList as bs && Ty.beq r r'
  | .struct a, .struct b => a == b
  | .ind a, .ind b => a == b
  | _, _ => false
@[expose] public def Ty.beqList : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.beq a b && Ty.beqList as bs
  | _, _ => false
end

/-- We have to write out the `BEq` instance by hand because the deriving handler cannot
handle the mutually-recursive `.fn` case. -/
public instance : BEq Ty :=
  ⟨Ty.beq⟩

mutual
public theorem Ty.beq_iff_eq : ∀ (a b : Ty), Ty.beq a b = true ↔ a = b
  | .bool, b => by cases b <;> simp [Ty.beq]
  | .int, b => by cases b <;> simp [Ty.beq]
  | .string, b => by cases b <;> simp [Ty.beq]
  | .option a, b => by cases b <;> simp [Ty.beq, Ty.beq_iff_eq a]
  | .except e a, b => by cases b <;> simp [Ty.beq, Ty.beq_iff_eq e, Ty.beq_iff_eq a]
  | .list a, b => by cases b <;> simp [Ty.beq, Ty.beq_iff_eq a]
  | .hashmap k v, b => by cases b <;> simp [Ty.beq, Ty.beq_iff_eq k, Ty.beq_iff_eq v]
  | .tuple as, b => by cases b <;> simp [Ty.beq, Ty.beqList_iff_eq as]
  | .fn as r, b => by cases b <;> simp [Ty.beq, Ty.beqList_iff_eq as, Ty.beq_iff_eq r]
  | .struct s, b => by cases b <;> simp [Ty.beq]
  | .ind s, b => by cases b <;> simp [Ty.beq]
public theorem Ty.beqList_iff_eq : ∀ (as bs : List Ty), Ty.beqList as bs = true ↔ as = bs
  | [], bs => by cases bs <;> simp [Ty.beqList]
  | a :: as, bs => by cases bs <;> simp [Ty.beqList, Ty.beq_iff_eq a, Ty.beqList_iff_eq as]
end

public instance : LawfulBEq Ty where
  eq_of_beq h := (Ty.beq_iff_eq _ _).mp h
  rfl := (Ty.beq_iff_eq _ _).mpr rfl

/-- We have to write out the `DecidableEq` instance by hand because the deriving handler cannot
handle the mutually-recursive `.fn` case. -/
public instance : DecidableEq Ty := fun a b => decidable_of_iff _ (Ty.beq_iff_eq a b)

mutual
public def Ty.renderWith (parens : Bool) : Ty → String
  | .bool => "bool"
  | .int => "int"
  | .string => "string"
  | .option t => s!"option {Ty.renderWith true t}"
  | .except e t => s!"except {Ty.renderWith true e} {Ty.renderWith true t}"
  | .list t => s!"list {Ty.renderWith true t}"
  | .hashmap k v => s!"hashmap {Ty.renderWith true k} {Ty.renderWith true v}"
  | .tuple ts => s!"tuple({Ty.renderGroup ts})"
  | .fn ps r =>
    let s := s!"({Ty.renderGroup ps}) -> {Ty.renderWith false r}"
    if parens then s!"({s})" else s
  | .struct name => s!"struct {name}"
  | .ind name => s!"inductive {name}"
public def Ty.renderGroup : List Ty → String
  | [] => ""
  | [t] => Ty.renderWith false t
  | t :: ts => s!"{Ty.renderWith false t}, {Ty.renderGroup ts}"
end

public def Ty.render (t : Ty) : String :=
  Ty.renderWith false t

public instance : ToString Ty :=
  ⟨Ty.render⟩

public inductive Expression where
  /-- A function, annotated with the name and type of each of its parameters. -/
  | lam : List (String × Ty) → Expression → Expression
  /-- Apply a function to its arguments. -/
  | app : Expression → List Expression → Expression
  | boolLit : Bool → Expression
  /-- A polymorphic conditional.

> if $expression1 then ( $expression2 ) else ( $expression3 )

The condition expression must be a boolean.  The two body expressions can be any type, as long
as it is the same for both. -/
  | ite : Expression → Expression → Expression → Expression
  /-- Conjunction of two booleans, short-circuiting.

> $expression1 && $expression2

-/
  | boolAnd : Expression → Expression → Expression
  /-- Disjunction of two booleans, short-circuiting.

> $expression1 || $expression2

-/
  | boolOr : Expression → Expression → Expression
  /-- Test if two values are equal via deep structural comparison.

The two operands must be of the same type.

Two structure values are equal if they are the same type and every field holds an equal value under
the same name.  By name rather than by position, so it does not matter which order either value was
built with: a `structNew` may write the declaration's fields in any order.

Two inductive values are equal if they are the same type, they were constructed with the same
constructor tags, and their values are pointwise equal.

Values of function type cannot be compared. -/
  | equals : Expression → Expression → Expression
  /-- Test if the first object is less than the second.

The operands of the comparison are required to be the same type.
This comparison is polymorphic over int, string, option, list, and tuples.
Tuple and list comparison are lexicographic per element, so a list that runs out first comes before
one that has not.  An empty option comes before one that holds a value.

`Ty.orderable` is the whole of which types this applies to.  A bool is not one of them, nor is a
struct or an inductive type: unlike `equals`, this claims no ordering for the types a declaration
names. -/
  | lt : Expression → Expression → Expression
  /-- Test if the first object is less than or equal to the second.

The operands of the comparison are required to be the same type.
This comparison is polymorphic over int, string, option, list, and tuples.
Tuple and list comparison are lexicographic per element, so a list that runs out first comes before
one that has not.  An empty option comes before one that holds a value.

The same comparison `lt` performs, read one answer wider: two equal values are the one pair the two
forms differ on. -/
  | le : Expression → Expression → Expression
  /-- Introduce a let binding.  Binds the first expression to the given name, which
    becomes available in the second expression. -/
  | let_ : String → Expression → Expression → Expression
  /-- A variable reference. -/
  | varRef : String → Expression
  /-- Create a new instance of the struct with the given name, binding each
    field to the given values. All fields must be initialized. -/
  | structNew : String → List (FieldName × Expression) → Expression
  /-- Get the field with the given name from the given expression (i.e., obj.field). -/
  | structGet : Expression → FieldName → Expression
  /-- Update the given struct object with new bindings for the named fields.

The list of fields is not permitted to be empty.

Example: { x with field1 = value1, field2 = value2 } -/
  | structUpdate : Expression → List (FieldName × Expression) → Expression
  /-- Create a new instance of an inductive type using the given constructor name. -/
  | indNew : String → CtorName → List Expression → Expression
  /-- Case analysis on a value of an inductive type: the expression to take apart, and one alternative
per constructor of its type.

Example: match c with | Red => 0 | Rgb(r, g, b) => r -/
  | indMatch : Expression → List (CtorName × List String × Expression) → Expression
  | intLit : Int → Expression
  | plus : Expression → Expression → Expression
  | minus : Expression → Expression → Expression
  /-- Return the minimum of two integer inputs -/
  | min : Expression → Expression → Expression
  /-- Return the maximum of two integer inputs -/
  | max : Expression → Expression → Expression
  | stringLit : String → Expression
  /-- The empty option value with its type to aid type checking. -/
  | optionNone : Ty → Expression
  /-- The option value holding another value. -/
  | optionSome : Expression → Expression
  /-- Case analysis on a value of option type: the expression to take apart, the expression to
evaluate when it holds nothing, and the name to bind that value to together with the expression
to evaluate under it.

This is a special form (instead of `indMatch`) because options get compiled away during extraction. -/
  | optionMatch : Expression → Expression → String → Expression → Expression
  /-- A successful `except`, holding the value it succeeded with, annotated with the type an error
would have had.

The annotation is there for the reason `optionNone`'s is, one half over: an `except` relates two
types and a success carries a value of only the second, so the error type is what nothing in the
expression says.  `optionSome` needs none because an option has one half and the value is it.

What it is *not* is the type of this expression: that is `except` of the annotation and the type
inferred for the value, so the payload type is still read off what is held, exactly as `optionSome`
reads it. -/
  | exceptOk : Ty → Expression → Expression
  /-- A failed `except`, holding the error, annotated with the type a success would have carried —
`exceptOk`'s annotation on the other side, and for the same reason. -/
  | exceptError : Ty → Expression → Expression
  /-- Case analysis on a value of except type: the expression to take apart, then the name to bind
the error to together with the expression to evaluate under it, then the same for the value a
success carries.

The error case comes first, the order `Except ε α` lists its constructors in and the order
`optionMatch` puts its empty case in.  Both cases bind a name, which is the whole of what separates
this from `optionMatch`: an error carries a value where an empty option carries nothing.

A special form rather than an `indMatch` for the reason `optionMatch` is one: the type names no
declaration, so there is no constructor list for a match to be exhaustive against — the form holds
both cases and nothing can be missing. -/
  | exceptMatch : Expression → String → Expression → String → Expression → Expression
  /-- The empty list annotated with its element type -/
  | lnil : Ty → Expression
  | lcons : Expression → Expression → Expression
  /-- Case analysis of list values.

  The arguments are:

  1. The expression to analyze
  2. The value to return when the list is nil
  3. The name to bind for the head of the list in the non-empty case
  4. The name to bind for the tail of the list in the non-empty case
  5. The expression to evaluate with those two names bound, for the non-empty list case
  -/
  | listMatch : Expression → Expression → String → String → Expression → Expression
  /-- Index into the given list with an integer index.

  > lst[idx]

  Returns none if the index is out of range and returns some(elt) otherwise. -/
  | listIndex : Expression → Expression → Expression
  /-- Map a function over lists.

For a list `l` of type `list a`, and a function `f` of type `(a) -> b`, `map l f` produces a `list b`.
-/
  | listMap : Expression → Expression → Expression
  /-- Map a function over lists to produce lists to concatenate.

  > flatMap (l : list a) (f : a → list b) : list b
  -/
  | listFlatMap : Expression → Expression → Expression
  /-- Calculate the length of the given list. -/
  | listLength : Expression → Expression
  /-- Find the index of the first element of the given list that matches the predicate.

  > findIndex : list α → (a → bool) → option int
  -/
  | listFindIndex : Expression → Expression → Expression
  | listReverse : Expression → Expression
  /-- Sort the given list, applying the given function to project out the sort key.

> sortOn lst (fun (item : ty) item.foo)

The first argument must be a list.
The projection function in the second argument takes a single argument of the same type as the elements of the list.  The return
type of the projection function must be comparable with the DSL less than operation. -/
  | listSortOn : Expression → Expression → Expression
  /-- Sort the given list, applying the given function to compare two elements

> sortBy lst (fun (item1 : ty) (item2 : ty) => item1 <= item2)

The first argument must be a list.
The second argument is a function that compares two elements and returns a boolean if
the first is less than or equal to the second.

`listSortOn`'s other half: a key is read off one element and the ordering is the key type's own, where
a comparison is handed two and answers for the pair itself.  So this is the one sort that asks nothing
of any type — `Ty.orderable` is what a key must satisfy and a `bool` is a `bool` — which is what lets
a list of structs be sorted by something no ordering reaches. -/
  | listSortBy : Expression → Expression → Expression
  | hashmapEmpty : Ty → Ty → Expression
  /-- Augment the given hashmap `m` with a binding of `k` to `v`

> hashmapPut m k v

Creates a new hashmap with the new binding, discarding any previous binding for `k`. -/
  | hashmapPut : Expression → Expression → Expression → Expression
  /-- Get the value bound to `k` in `m`, if any.  Returns an `option v`.

> hashampGet m k
-/
  | hashmapGet : Expression → Expression → Expression
  /-- Map a function over a hashmap to produce a new hashmap.

Given a hashmap of type hashmap(k, v1), the mapping function is of type fun(k, v1) -> v2,
producing a hashmap of type hashmap(k, v2). -/
  | hashmapMap : Expression → Expression → Expression
  /-- Convert a hashmap to a list of pairs. -/
  | hashmapToList : Expression → Expression
  /-- Create a new tuple with the given elements.

> tupleNew [$expression1, $expression2, ...]

with concrete syntax tuple($expression1, $expression2, ...).

A `List Expression`, the way `Ty.tuple` holds a `List Ty` and `Value.tuple` a `List Value`: a tuple
is positional, so the elements are given in the order their types come in and there is nothing to
name.  How many there are is not checked against anything — a tuple type is whatever types the
elements turned out to have, unlike `indNew`, whose arity is its declaration's.  `tupleNew []` is
the one value of `tuple []`. -/
  | tupleNew : List Expression → Expression
  /-- Get an element from a tuple.

> tupleGet $tuple $index

with concrete syntax t.N where N is the index.

The index is a `Nat` rather than an `Expression`, which is what makes this typeable at all: a tuple
is heterogeneous, so what comes out is of the type its tuple type gives at that position, and a
position arrived at by evaluating something would be one no `Ty` could be read off.  That is the
same reason `structGet` takes a `FieldName` rather than an expression — this is its positional
counterpart, over a type that carries its own fields instead of naming a declaration. -/
  | tupleGet : Expression → Nat → Expression
  /-- A branch nothing reaches, at the type that branch needed.

> unreachable $type $why

with concrete syntax unreachable "$why" : $type.

This expression is used on branches that are intended to be proved unreachable.  `Eval` has no rule
for it, so an expression reaching one is stuck: `Eval td env e v` is a premise everywhere in this
development, so a proof that a declaration produces a value at all is a proof that no `unreachable`
in it was reached.  That is what makes a use of this safe rather than merely untested.  Because they
need to be proved unreachable, they do not need to be extracted.

The type is an annotation, the way `lnil`'s and `optionNone`'s are, rather than something read off
what the expression holds: every form determines its own type (see `Expression.inferE`), so an
expression that could have had any of them is one nothing could report a type for.  Writing the
annotation is what lets it have the type its branch's siblings have, which is the whole of what
having any type is for here.

The `String` says why the branch cannot be reached and goes nowhere: nothing reads it, since nothing
reaches it. -/
  | unreachable : Ty → String → Expression

public structure FuncDecl where
  docstring : String
  name : String
  parameters : List (String × Ty)
  body : Expression
  resultType : Ty

/-- A whole program.

See the type checker for the definition of well-formedness.  In brief, any referenced types must be
declared as either structure types or inductives.  Order does not matter, but the order will be
preserved during extraction.  Names must each be unique. -/
public structure Program where
  funcDecls : List FuncDecl
  structDecls : List StructDecl := []
  inductiveDecls : List InductiveDecl := []
