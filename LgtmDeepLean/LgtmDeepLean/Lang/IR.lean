module


public inductive Ty where
| bool
| int
| string
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

The `name` is the name of the introduced type.  Each constructor has a name and a list of
data types contained in that constructor.  The list of types may be empty for trivial enums.

A `Ty.ind` only carries the name, so this is the only place a constructor's data types are recorded,
and every rule about an inductive goes through the declaration the name resolves to — the same
division of labour `StructDecl` and `Ty.struct` are in.  What resolving a name means is
`Inductives.lookup`'s business, and `Program.InductiveNamesUnique` is what rules out the case where
the order of declarations decides it.

No two constructors may share a name, which is `InductiveDecl.CtorNamesUnique`: the list is an
association list read with `List.lookup`, so a second constructor of a name already used declares
data types nothing could build a value at.  `Program.check` turns down a declaration that has one,
the way it does a structure declaration repeating a field.  A constructor name is scoped to its own
type, though — `indNew` names the type as well — so two declarations may each have a `Red`.

The order the constructors are written in is then the declaration's own and decides nothing at all:
an `Expression.indMatch` names the constructor each of its alternatives is for, so it may give them
in whatever order suits it.  What is positional is a constructor's data, which has no names of its
own; the names belong to the match alternative that takes it apart.

Recursion needs no special treatment.  A constructor's data types are `Ty`s like any other, and a
type name is resolved where it is mentioned rather than where it was declared, so `ind "Tree"` may
appear among a `Tree`'s own constructors.  A *value* of such a type is finite all the same: `Eval`
builds one out of values that already exist, so no cycle can arise from it. -/
public structure InductiveDecl where
  name : String
  constructors : List (CtorName × List Ty)
  deriving Repr

/-! `Ty` is a nested inductive because `fn` holds a `List Ty`.  The `DecidableEq` deriving handler
cannot handle this, so we write out equality by hand.  The recursion is mutual with a version over
lists of types, which is how `Ty.rec` offers the nesting: one motive for `Ty`, one for `List Ty`. -/

mutual

public def Ty.beq : Ty → Ty → Bool
  | .bool, .bool => true
  | .int, .int => true
  | .string, .string => true
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

public instance : BEq Ty := ⟨Ty.beq⟩

mutual

public theorem Ty.beq_iff_eq : ∀ (a b : Ty), Ty.beq a b = true ↔ a = b
  | .bool, b => by cases b <;> simp [Ty.beq]
  | .int, b => by cases b <;> simp [Ty.beq]
  | .string, b => by cases b <;> simp [Ty.beq]
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

public instance : DecidableEq Ty := fun a b => decidable_of_iff _ (Ty.beq_iff_eq a b)

public inductive Expression where
/-- A function, annotated with the name and type of each of its parameters -/
| lam : List (String × Ty) → Expression → Expression
/-- Apply a function to all of its arguments at once -/
| app : Expression → List Expression → Expression
| boolLit : Bool → Expression
/-- A polymorphic conditional.

    > if $expression1 then { $expression2 } else { $expression3 }

    The condition expression must be a boolean.  The two body expressions can be any type, as long
    as it is the same for both. -/
| ite : Expression → Expression → Expression → Expression
/-- Test if two values are equal via deep structural comparison.

The two operands must be of the same type.

Two structure values are equal if they are the same type and all of their fields are pointwise equal.

Two inductive values are equal if they are the same type, they were constructed with the same constructor tags, and their values are pointwise equal.

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
/-- Apply one of a declared inductive type's constructors: the type's name, the constructor's name,
and one expression per data type that constructor declares.

The type's name is given as well as the constructor's because the type is what a declaration is found
under: two inductive types may each declare a constructor called `Empty`, and a constructor name on
its own would be a search rather than a lookup.  It is the same reason `structNew` names the struct
it builds.

Example: new Color.Rgb(255, 0, 0) -/
| indNew : String → CtorName → List Expression → Expression
/-- Case analysis on a value of an inductive type: the expression to take apart, and one alternative
per constructor of its type.

An alternative is the constructor's name, one binding name per data type that constructor carries,
and the expression to evaluate when the value was built by it.  The names are the alternative's own —
a constructor's data is positional — and they are in scope in that alternative's expression only.

The alternatives have to be the declaration's constructors, one apiece, which is what makes this
exhaustive: there is no default alternative, and no way to leave a constructor out or to name one
twice.  They may come in any order, the declaration's or another, since each one says which
constructor it is for.  Every alternative also has to produce the same type, since the expression has
one type however the value was built.

Example: match c with | Red => 0 | Rgb(r, g, b) => r -/
| indMatch : Expression → List (CtorName × List String × Expression) → Expression
| intLit : Int → Expression
| plus : Expression → Expression → Expression
| minus : Expression → Expression → Expression
| stringLit : String → Expression
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

/-- A whole program: the declarations it is made of, in the order they were written, and the
structure types they may mention.

There is no entry point, because nothing here needs one: a program is what a `FuncDecl` is checked
and evaluated *against*, and which of its declarations gets called is the caller's business.

Order is kept rather than sorted into a map so that a program is exactly the list of `lgtm def`s a
file contains.  What it means for a name to resolve is then `Program.lookup`'s business, and
`Program.NamesUnique` is what rules out the case where the order decides it.

`structDecls` is where every structure type in the program is declared: a `Ty.struct` names one of
these and nothing else.  Declaring them at the top level rather than inside an expression is what
lets two declarations pass the same struct to each other, and `Program.StructNamesUnique` is the
counterpart of `Program.NamesUnique` for them, with `Program.FieldNamesUnique` the condition inside
each one.  It defaults to empty so that a program using no structs is written exactly as before.

`inductiveDecls` is the same thing for inductive types, which a `Ty.ind` names the way a `Ty.struct`
names a structure type, with `Program.InductiveNamesUnique` and `Program.CtorNamesUnique` as the
two conditions answering to those.  The two lists are separate rather than one list of type
declarations because the two kinds of type are taken apart by different forms, and so are resolved
in different tables: `Program.typeDecls` is where they are bundled back together as the one thing
checking and evaluation take. -/
public structure Program where
  funcDecls : List FuncDecl
  structDecls : List StructDecl := []
  inductiveDecls : List InductiveDecl := []
