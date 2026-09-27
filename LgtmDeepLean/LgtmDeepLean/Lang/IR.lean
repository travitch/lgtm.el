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
structs is written exactly as before. -/
public structure Program where
  funcDecls : List FuncDecl
  structDecls : List StructDecl := []
