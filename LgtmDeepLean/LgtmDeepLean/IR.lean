module

public inductive Ty where
| int
| list : Ty → Ty
  deriving Repr, DecidableEq

public def Ty.denote : Ty → Type
| .int => Int
| .list t => List t.denote

public inductive Expression where
| varRef : String → Expression
| intLit : Int → Expression
| plus : Expression → Expression → Expression
| minus : Expression → Expression → Expression
/-- The empty list annotated with its element type -/
| lnil : Ty → Expression
| lcons : Expression → Expression → Expression

public structure Decl where
  docstring : String
  name : String
  parameters : List (String × Ty)
  body : Expression
  resultType : Ty
