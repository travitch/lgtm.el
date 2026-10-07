module


public inductive Ty where
| bool
| int
| string
| option : Ty → Ty
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

public abbrev FieldName := String

/-- A structure type declaration with named and typed fields.

Field names must be unique (see `StructDecl.FieldNamesUnique` [ref:struct_field_names_unique]). -/
public structure StructDecl where
  name : String
  fields : List (FieldName × Ty)
  deriving Repr

public abbrev CtorName := String

/-- A declaration of an inductive type that is similar to Lean's built-in inductives.

Inductive constructor names are required to be unique (`InductiveDecl.CtorNamesUnique`
[ref:inductive_constructor_names_unique]).  Constructor names may be reused across unrelated
inductives. -/
public structure InductiveDecl where
  name : String
  constructors : List (CtorName × List Ty)
  deriving Repr

mutual

public def Ty.beq : Ty → Ty → Bool
  | .bool, .bool => true
  | .int, .int => true
  | .string, .string => true
  | .option a, .option b => Ty.beq a b
  | .list a, .list b => Ty.beq a b
  | .hashmap k1 v1, .hashmap k2 v2 => Ty.beq k1 k2 && Ty.beq v1 v2
  | .tuple as, .tuple bs => Ty.beqList as bs
  | .fn as r, .fn bs r' => Ty.beqList as bs && Ty.beq r r'
  | .struct a, .struct b => a == b
  | .ind a, .ind b => a == b
  | _, _ => false

public def Ty.beqList : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.beq a b && Ty.beqList as bs
  | _, _ => false

end

/-- We have to write out the `BEq` instance by hand because the deriving handler cannot
handle the mutually-recursive `.fn` case. -/
public instance : BEq Ty := ⟨Ty.beq⟩

mutual

public theorem Ty.beq_iff_eq : ∀ (a b : Ty), Ty.beq a b = true ↔ a = b
  | .bool, b => by cases b <;> simp [Ty.beq]
  | .int, b => by cases b <;> simp [Ty.beq]
  | .string, b => by cases b <;> simp [Ty.beq]
  | .option a, b => by cases b <;> simp [Ty.beq, Ty.beq_iff_eq a]
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

public inductive Expression where
/-- A function, annotated with the name and type of each of its parameters. -/
| lam : List (String × Ty) → Expression → Expression
/-- Apply a function to its arguments. -/
| app : Expression → List Expression → Expression
| boolLit : Bool → Expression
/-- A polymorphic conditional.

> if $expression1 then { $expression2 } else { $expression3 }

The condition expression must be a boolean.  The two body expressions can be any type, as long
as it is the same for both. -/
| ite : Expression → Expression → Expression → Expression
/-- Test if two values are equal via deep structural comparison.

The two operands must be of the same type.

Two structure values are equal if they are the same type and all of their fields are pointwise
equal.

Two inductive values are equal if they are the same type, they were constructed with the same
constructor tags, and their values are pointwise equal.

Values of function type cannot be compared. -/
| equals : Expression → Expression → Expression
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
/-- The empty list annotated with its element type -/
| lnil : Ty → Expression
| lcons : Expression → Expression → Expression
/-- Calculate the length of the given list. -/
| listLength : Expression → Expression
| listReverse : Expression → Expression
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
