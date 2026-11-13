module

public import LgtmDeepLean.Lang.IR
public import LgtmDeepLean.Lang.TypeCheck.Comparable
public import LgtmDeepLean.Lang.TypeCheck.Infer
public import LgtmDeepLean.Lang.TypeCheck.TypeDecls
public import LgtmDeepLean.Lang.TypeCheck.Uniqueness

/-- Check `e` against the expected type `ty` under `ctx`, or describe why it does not check. -/
@[expose] public def Expression.check (td : TypeDecls) (ctx : Context) (e : Expression) (ty : Ty) :
    Except String Unit :=
  (e.inferE td ctx).expect ty "this expression"

/-- `e` checks against `ty` exactly when `ty` is the type inferred for it, which is what the
message `Expression.check` carries says nothing about. -/
@[simp, grind =] public theorem Expression.check_eq_ok {td : TypeDecls} {ctx : Context}
    {e : Expression} {ty : Ty} {u : Unit} :
    e.check td ctx ty = .ok u ↔ e.infer td ctx = some ty := by
  simp [Expression.check, Expression.inferE_eq_ok_iff]

/-- `e` is well typed under `ctx` at some type. -/
public def Expression.WellTyped (td : TypeDecls) (ctx : Context) (e : Expression) : Prop :=
  ∃ t, e.check td ctx t = .ok ()

/-- Inference is complete for well-typed expressions: since every form carries enough
information to determine its own type, a type exists exactly when `infer` finds one. -/
public theorem Expression.wellTyped_iff_infer_isSome (td : TypeDecls) (ctx : Context)
    (e : Expression) : e.WellTyped td ctx ↔ (e.infer td ctx).isSome := by
  simp [Expression.WellTyped, Option.isSome_iff_exists]

/-! ## Globals

Checking the declarations a body may mention besides its own parameters.  The table itself —
`Globals`, and the `Program` projection that builds one — is in
`LgtmDeepLean.Lang.TypeCheck.TypeDecls`; what is here is the context a table supplies and what it
means for every entry of it to check. -/

/-- The type a declaration has where its name is mentioned: a function from its parameters' types
to its result type.

A declaration of no parameters gets `.fn [] t` rather than `t`, which is what makes a global
variable a call. -/
@[expose] public def FuncDecl.ty (d : FuncDecl) : Ty := .fn (d.parameters.map Prod.snd) d.resultType

/-- The context `gs` supplies: every global's name at the type of the declaration stored for it. -/
@[expose] public def Globals.types : Globals → Context
  | [] => []
  | (x, d) :: gs => (x, d.ty) :: Globals.types gs

@[simp] public theorem Globals.types_nil : Globals.types [] = [] := by simp [Globals.types]

@[simp] public theorem Globals.types_cons (x : String) (d : FuncDecl) (gs : Globals) :
    Globals.types ((x, d) :: gs) = (x, d.ty) :: Globals.types gs := by simp [Globals.types]

/-- `Globals.types` is `FuncDecl.ty` under the lookup, which is how a proof gets from the type a
name was inferred at back to the declaration that gave it. -/
@[simp, grind =] public theorem Globals.lookup_types {gs : Globals} {x : String} :
    (Globals.types gs).lookup x = (gs.lookup x).map FuncDecl.ty := by
  induction gs with
  | nil => rfl
  | cons p gs ih =>
      obtain ⟨k, d⟩ := p
      by_cases h : x == k <;> simp [Globals.types, List.lookup_cons, h, ih]

/-- Type check a declaration. -/
@[expose] public def FuncDecl.check (d : FuncDecl) (td : TypeDecls) (gs : Globals) : Except String Unit :=
  (d.body.check td (d.parameters ++ Globals.types gs) d.resultType).mapError
    fun m => s!"in the body of '{d.name}': {m}"

/-- `d`'s body agrees with the types `d` declares for its parameters and its result, given `td` and
`gs`. -/
public def FuncDecl.WellTyped (d : FuncDecl) (td : TypeDecls) (gs : Globals) : Prop :=
  d.check td gs = .ok ()

/-- What `WellTyped` says, with the message dropped: inference on the body finds exactly the
declared result type.  This is how a proof reads it where the declaration is not a literal; where it
is, running `FuncDecl.check` decides it. -/
@[simp, grind =] public theorem FuncDecl.wellTyped_iff_infer_eq_some {d : FuncDecl} {td : TypeDecls}
    {gs : Globals} :
    d.WellTyped td gs ↔ d.body.infer td (d.parameters ++ Globals.types gs) = some d.resultType := by
  simp [FuncDecl.WellTyped, FuncDecl.check]

/-- Every declaration in `gs` checks, each under a context holding all of them.

Itself included — which is what lets a global call itself, and two globals call each other.  This
is a condition on syntax alone: no value occurs in it.  That is what keeps it provable at all.  A
value-level version would have to type each global's closure, which carries the globals table,
which would need typing again, and no inductive relation survives that regress.

Exposed because it is a specification rather than an algorithm: there is nothing in it for an
inversion principle to recover, and every consumer needs to instantiate it at a name. -/
@[expose] public def Globals.WellTyped (td : TypeDecls) (gs : Globals) : Prop :=
  ∀ x d, gs.lookup x = some d → d.WellTyped td gs

/-- A program with no globals has nothing to check, whatever structs it declares. -/
public theorem Globals.wellTyped_nil {td : TypeDecls} : Globals.WellTyped td [] := by
  intro x d hx; simp at hx

/-- A lookup only ever hands back an entry the table contains. -/
public theorem Globals.mem_of_lookup {gs : Globals} {x : String} {d : FuncDecl}
    (h : gs.lookup x = some d) : (x, d) ∈ gs :=
  List.mem_of_lookup h

/-- A table checks if each of its entries does.

Stated over membership rather than lookup because that is what a table written out as a literal can
be discharged against, one entry at a time. -/
public theorem Globals.wellTyped_of_forall {td : TypeDecls} {gs : Globals}
    (h : ∀ p ∈ gs, FuncDecl.WellTyped p.2 td gs) : Globals.WellTyped td gs :=
  fun x d hx => h (x, d) (Globals.mem_of_lookup hx)

/-- Check every declaration in `ds`, each under the table `gs`, and stop at the first one that does
not check.

The list to walk is the unnamed parameter.  A list of all of the globals (`gs`) is also
passed in so that globals can refer to each other during checking. -/
@[expose] public def Globals.checkEach (td : TypeDecls) (gs : Globals) : Globals → Except String Unit
  | [] => .ok ()
  | (_, d) :: ds => do
    d.check td gs
    Globals.checkEach td gs ds

/-- A walk succeeds exactly when every entry it passed checks. -/
private theorem Globals.checkEach_eq_ok {td : TypeDecls} {gs ds : Globals} :
    Globals.checkEach td gs ds = .ok () ↔ ∀ p ∈ ds, p.2.WellTyped td gs := by
  induction ds with
  | nil => simp [Globals.checkEach]
  | cons p ds ih =>
      obtain ⟨x, d⟩ := p
      simp [Globals.checkEach, FuncDecl.WellTyped, ih]

/-- Run the checker over a whole table, stopping at the first entry that does not check.  Decides
`Globals.WellTyped` — `Except.isOk` of this is what a `#guard` over a table asks — even where the
kernel cannot reduce `Expression.infer`. -/
@[expose] public def Globals.check (td : TypeDecls) (gs : Globals) : Except String Unit :=
  Globals.checkEach td gs gs

/-- `Globals.check` is what it says it is.  It is the stronger of the two: it checks every entry,
where `Globals.WellTyped` only constrains the ones a lookup can reach. -/
public theorem Globals.wellTyped_of_check {td : TypeDecls} {gs : Globals}
    (h : Globals.check td gs = .ok ()) : Globals.WellTyped td gs :=
  Globals.wellTyped_of_forall fun p hp => Globals.checkEach_eq_ok.mp h p hp

/-! ## Programs

Checking a whole `Program`.  The tables it presents — `Program.globals`, `Program.typeDecls` and
the lookups through them — are in `LgtmDeepLean.Lang.TypeCheck.TypeDecls`, and the conditions under
which those lookups resolve every declaration are in `LgtmDeepLean.Lang.TypeCheck.Uniqueness`. -/

/-- The first name a list repeats.

This is used to construct error messages. -/
public def List.firstRepeat : List String → Option String
  | [] => none
  | n :: ns => if ns.contains n then some n else List.firstRepeat ns

/-- Which structure declaration declares a field name twice, and which name that is. -/
public def Program.fieldNamesProblem (p : Program) : String :=
  match p.structDecls.findSome? fun sd =>
      (List.firstRepeat (sd.fields.map Prod.fst)).map fun f => (sd.name, f) with
  | some (name, f) => s!"struct '{name}' declares the field '{f}' twice"
  | none => "a struct declares a field twice"

/-- Which inductive declaration declares a constructor name twice, and which name that is. -/
public def Program.ctorNamesProblem (p : Program) : String :=
  match p.inductiveDecls.findSome? fun d =>
      (List.firstRepeat (d.constructors.map Prod.fst)).map fun c => (d.name, c) with
  | some (name, c) => s!"inductive '{name}' declares the constructor '{c}' twice"
  | none => "an inductive declares a constructor twice"

/-- Check a whole program: the types it declares are well formed, and every declaration checks
against the signatures of all of them, its own included, and against those types.

Well formed is `Program.FieldNamesUnique` and `Program.CtorNamesUnique`: a field or a constructor
declared twice is one the rest of the language cannot reach, so a declaration carrying one is
rejected here rather than left to mean less than it says.  Neither is a condition on any expression,
which is why they are checked once over the declarations instead of anywhere in `Expression.infer`.

The conditions across declarations are not part of this; see
`LgtmDeepLean.Lang.TypeCheck.Uniqueness`. -/
@[expose] public def Program.check (p : Program) : Except String Unit :=
  if p.FieldNamesUnique then
    if p.CtorNamesUnique then Globals.check p.typeDecls p.globals
    else .error p.ctorNamesProblem
  else .error p.fieldNamesProblem

/-- Every declaration in `p` checks, under `p`. -/
@[expose] public def Program.WellTyped (p : Program) : Prop :=
  Globals.WellTyped p.typeDecls p.globals

/-- `Program.check` is the stronger of the two, as `Globals.check` is: it also has the type
declarations to be well formed, which `Program.WellTyped` says nothing about. -/
public theorem Program.wellTyped_of_check {p : Program} (h : p.check = .ok ()) : p.WellTyped := by
  simp only [Program.check] at h
  split at h
  · split at h
    · exact Globals.wellTyped_of_check h
    · simp at h
  · simp at h

/-- The other half of what `Program.check` decided: no structure declaration repeats a field name.
A condition on the declarations rather than on any expression, which is why it is read off the
check's result here instead of appearing in `Program.WellTyped`. -/
public theorem Program.fieldNamesUnique_of_check {p : Program} (h : p.check = .ok ()) :
    p.FieldNamesUnique := by
  simp only [Program.check] at h
  split at h
  · assumption
  · simp at h

/-- And no inductive declaration repeats a constructor name. -/
public theorem Program.ctorNamesUnique_of_check {p : Program} (h : p.check = .ok ()) :
    p.CtorNamesUnique := by
  simp only [Program.check] at h
  split at h
  · split at h
    · assumption
    · simp at h
  · simp at h

/-- Everything a well-typed program declares is well typed under it. -/
public theorem Program.wellTyped_decl {p : Program} (hp : p.WellTyped) (hu : p.NamesUnique)
    {d : FuncDecl} (hd : d ∈ p.funcDecls) : d.WellTyped p.typeDecls p.globals :=
  hp d.name d (Program.lookup_self hu hd)
