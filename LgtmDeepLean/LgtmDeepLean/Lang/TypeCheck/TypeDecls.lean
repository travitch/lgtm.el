module

public import LgtmDeepLean.Lang.IR

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
