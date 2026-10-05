module


public inductive Ty where
| bool
| int
| string
/-- A value of the given type, or nothing.

This behaves like an inductive type of two constructors — `Expression.optionNone` and
`Expression.optionSome` build one, and `Expression.optionMatch` takes one apart — but it is a type
former of its own rather
than an `InductiveDecl`, because extraction gives it a representation of its own and erases the
constructors.  That is also why it needs no declaration to be well formed: unlike `.struct` and
`.ind`, which are nominal and name something a `TypeDecls` has to resolve, this one carries its
element type. -/
| option : Ty → Ty
| list : Ty → Ty
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
/-- The empty option value with its type to aid type checking.

Spelled `optionNone` rather than `none` for the reason every other form carries the name of the type
it belongs to — `indNew`, `structNew` — and for one more: a constructor called `Expression.none`
would shadow `Option.none` inside every declaration in the `Expression` namespace, which is most of
the type checker. -/
| optionNone : Ty → Expression
/-- The option value holding another value. -/
| optionSome : Expression → Expression
/-- Case analysis on a value of option type: the expression to take apart, the expression to
evaluate when it holds nothing, and — for when it holds a value — the name to bind that value to
together with the expression to evaluate under it.

`indMatch` specialised to `Ty.option`, and specialised in the two ways that matter.  The cases are
the two the type has rather than a list of alternatives, so there is no exhaustiveness to check and
no constructor name to resolve: an `option` carries its element type instead of naming a declaration,
so the type of the name bound is read off the scrutinee.  And an `optionSome` carries one value
rather than a list of them, so one name is bound rather than as many as a declaration gives.

Example: match o with | none => 0 | some(x) => x -/
| optionMatch : Expression → Expression → String → Expression → Expression
/-- The empty list annotated with its element type -/
| lnil : Ty → Expression
| lcons : Expression → Expression → Expression
| listReverse : Expression → Expression

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
