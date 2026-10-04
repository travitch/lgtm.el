module

public import LgtmDeepLean.Lang.IR

/-! # The type declarations in scope

What a program's struct and inductive declarations look like once they are something to be looked up
in rather than a list to be read through, which is how everything downstream of `IR` takes them: the
type checker, the comparability walk, `Value.HasType` and `Eval` all resolve a type's name against
the same two tables.

Only the tables are here.  What is asked of them — that no two entries share a name, that a lookup
finds what a declaration put there — belongs to whoever asks, and is in
`LgtmDeepLean.Lang.TypeCheck` with the other uniqueness conditions. -/

/-- The structure types in scope everywhere, keyed by the names they declare. -/
public abbrev Structs := List (String × StructDecl)

/-- Key each structure declaration by the name it declares. -/
@[expose] public def Structs.ofDecls (sds : List StructDecl) : Structs :=
  sds.map fun s => (s.name, s)

@[simp] public theorem Structs.ofDecls_nil : Structs.ofDecls [] = [] := by simp [Structs.ofDecls]

@[simp] public theorem Structs.ofDecls_cons (s : StructDecl) (sds : List StructDecl) :
    Structs.ofDecls (s :: sds) = (s.name, s) :: Structs.ofDecls sds := by simp [Structs.ofDecls]

/-- The inductive types in scope everywhere, keyed by the names they declare. -/
public abbrev Inductives := List (String × InductiveDecl)

/-- Key each inductive declaration by the name it declares. -/
@[expose] public def Inductives.ofDecls (ids : List InductiveDecl) : Inductives :=
  ids.map fun d => (d.name, d)

@[simp] public theorem Inductives.ofDecls_nil : Inductives.ofDecls [] = [] := by
  simp [Inductives.ofDecls]

@[simp] public theorem Inductives.ofDecls_cons (d : InductiveDecl) (ids : List InductiveDecl) :
    Inductives.ofDecls (d :: ids) = (d.name, d) :: Inductives.ofDecls ids := by
  simp [Inductives.ofDecls]

/-- The type declarations in scope everywhere in a given program. -/
public structure TypeDecls where
  ss : Structs := []
  is : Inductives := []
  deriving Repr
