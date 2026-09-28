module


public inductive Ty where
| int
| string
| list : Ty → Ty
/-- A function from the types of its parameters to the type of its result. -/
| fn : List Ty → Ty → Ty
/-- A declared structure type, named rather than spelled out: the fields live in the `StructDecl`
the name resolves to.

Structs are therefore *nominal*.  Two of these are the same type exactly when their names agree, so
two declarations with the same fields under different names are unrelated, and a struct type says
nothing at all until there is a table to resolve the name in. -/
| struct : String → Ty
/-- A declared inductive type, named rather than spelled out: the constructors live in the
`InductiveDecl` the name resolves to.

Nominal in exactly the way `struct` is, and for the same reason: the name is the whole type, so two
declarations listing the same constructors are unrelated types and neither says anything until there
is a table to resolve its name in. -/
| ind : String → Ty
  deriving Repr

public abbrev FieldName := String

/-- A structure type declaration: the name the type is referred to by, and the fields it has, in the
order they were written, each with its type.

A `Ty.struct` only carries the name, so this is the only place a field's type is recorded and every
rule about a struct goes through the declaration the name resolves to.  What resolving a name means
is `Structs.lookup`'s business, and `Program.StructNamesUnique` is what rules out the case where
the order of declarations decides it. -/
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

The order the constructors are written in is part of the declaration: a `Expression.indMatch` has to
give its alternatives in that order, which is what makes exhaustiveness one comparison rather than a
search.  The data types are positional and have no names of their own; the names belong to the match
alternative that takes them apart.

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

The alternatives have to be the declaration's constructors, in the declaration's order, which is what
makes this exhaustive: there is no default alternative, and no way to leave a constructor out or to
name one twice.  Every alternative also has to produce the same type, since the expression has one
type however the value was built.

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
counterpart of `Program.NamesUnique` for them.  It defaults to empty so that a program using no
structs is written exactly as before.

`inductiveDecls` is the same thing for inductive types, which a `Ty.ind` names the way a `Ty.struct`
names a structure type, with `Program.InductiveNamesUnique` as its uniqueness condition.  The two
lists are separate rather than one list of type declarations because the two kinds of type are taken
apart by different forms, and so are resolved in different tables: `Program.typeDecls` is where they
are bundled back together as the one thing checking and evaluation take. -/
public structure Program where
  funcDecls : List FuncDecl
  structDecls : List StructDecl := []
  inductiveDecls : List InductiveDecl := []
