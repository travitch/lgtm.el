module

public inductive Ty where
| int
| string
| list : Ty → Ty
/-- A function from the types of its parameters to the type of its result. -/
| fn : List Ty → Ty → Ty
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
/-- A variable reference. -/
| varRef : String → Expression
| intLit : Int → Expression
| plus : Expression → Expression → Expression
| minus : Expression → Expression → Expression
| stringLit : String → Expression
/-- The empty list annotated with its element type -/
| lnil : Ty → Expression
| lcons : Expression → Expression → Expression
| listReverse : Expression → Expression

public structure Decl where
  docstring : String
  name : String
  parameters : List (String × Ty)
  body : Expression
  resultType : Ty

/-- A whole program: the declarations it is made of, in the order they were written.

There is no entry point, because nothing here needs one: a program is what a `Decl` is checked and
evaluated *against*, and which of its declarations gets called is the caller's business.

Order is kept rather than sorted into a map so that a program is exactly the list of `lgtm def`s a
file contains.  What it means for a name to resolve is then `Program.lookup`'s business, and
`Program.NamesUnique` is what rules out the case where the order decides it. -/
public structure Program where
  decls : List Decl
