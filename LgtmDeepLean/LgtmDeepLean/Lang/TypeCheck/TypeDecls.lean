module

public import LgtmDeepLean.Lang.IR

/-! # Declaration tables

The tables a program's declarations are keyed into, one per kind of declaration, and the projections
that build them from a `Program`.  Everything here is an association list from a name to the
declaration written under it, or a bundle of such lists: this module is the shape the declarations
are read through, and nothing in it checks anything. -/

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

/-! ## Globals

The declarations a body may mention besides its own parameters.  A `Globals` is a table of
*declarations*, not of values: every global is a function, and a global variable is a function of
no arguments, written `g()`.

One mechanism covers both because recursion needs it to.  A table of values would have to be built
before anything could mention it, so a declaration could never refer to itself or to one defined
after it; a table of declarations is just syntax, and a body can be checked against a context
listing every entry including its own. -/

/-- The declarations in scope everywhere, each under the name it is referred to by. -/
public abbrev Globals := List (String × FuncDecl)

/-- Key each declaration by the name it declares. -/
@[expose] public def Globals.ofDecls (ds : List FuncDecl) : Globals := ds.map fun d => (d.name, d)

@[simp] public theorem Globals.ofDecls_nil : Globals.ofDecls [] = [] := by simp [Globals.ofDecls]

@[simp] public theorem Globals.ofDecls_cons (d : FuncDecl) (ds : List FuncDecl) :
    Globals.ofDecls (d :: ds) = (d.name, d) :: Globals.ofDecls ds := by simp [Globals.ofDecls]

/-! ## Programs

A `Program` is the source-level artifact — a file's worth of declarations — where a `Globals` is the
table those declarations are checked and run against.  `Program.globals` is the bridge.

Each definition below is exposed: a projection or an alias with nothing an inversion principle could
recover.  `Program.check` is not, for the same reason `Globals.check` is not — it runs
`Expression.infer`, which stays hidden. -/

/-- The globals table `p` presents to its own bodies: each declaration under the name it declares.

Derived rather than stored, so a declaration can never be filed under a name other than its own. -/
@[expose] public def Program.globals (p : Program) : Globals := Globals.ofDecls p.funcDecls

/-- The struct table `p` presents to its own bodies: each structure type under the name it declares.

Derived the same way and for the same reason as `Program.globals`. -/
@[expose] public def Program.structs (p : Program) : Structs := Structs.ofDecls p.structDecls

/-- The inductive table `p` presents to its own bodies: each inductive type under the name it
declares.  Derived the same way and for the same reason as `Program.globals`. -/
@[expose] public def Program.inductives (p : Program) : Inductives :=
  Inductives.ofDecls p.inductiveDecls

/-- The type declarations `p` presents to its own bodies, as the one bundle everything that resolves
a type name takes.

This is what `p` is checked and evaluated against, so a kind of declaration added to `Program` is
added here too and nowhere else. -/
@[expose] public def Program.typeDecls (p : Program) : TypeDecls where
  ss := p.structs
  is := p.inductives

/-- The declaration `x` names in `p`, or `none` if it names nothing. -/
@[expose] public def Program.lookup (p : Program) (x : String) : Option FuncDecl :=
  p.globals.lookup x

/-- The structure type `name` names in `p`, or `none` if it names nothing. -/
@[expose] public def Program.lookupStruct (p : Program) (name : String) : Option StructDecl :=
  p.structs.lookup name

/-- The inductive type `name` names in `p`, or `none` if it names nothing. -/
@[expose] public def Program.lookupInductive (p : Program) (name : String) : Option InductiveDecl :=
  p.inductives.lookup name
