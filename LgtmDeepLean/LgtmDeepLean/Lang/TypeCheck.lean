module

public import LgtmDeepLean.Lang.IR
public import LgtmDeepLean.Lang.TypeCheck.Comparable
public import LgtmDeepLean.Lang.TypeCheck.Infer
public import LgtmDeepLean.Lang.TypeCheck.TypeDecls
public import LgtmDeepLean.Lang.TypeCheck.Uniqueness

/-! # Type checking

Checking, as against inferring: an expression against an expected type, a declaration against the
signature it gives itself, and a program against all of it.  Inference is what each of these rests
on and it is in `LgtmDeepLean.Lang.TypeCheck.Infer`, so checking an expression is one comparison and
the rest of this module is which context each declaration is checked under. -/

/-- Check `e` against the expected type `ty` under `ctx`. -/
public def Expression.check (td : TypeDecls) (ctx : Context) (e : Expression) (ty : Ty) : Bool :=
  e.infer td ctx == some ty

/-- `e` is well typed under `ctx` at some type. -/
public def Expression.WellTyped (td : TypeDecls) (ctx : Context) (e : Expression) : Prop :=
  ∃ t, e.check td ctx t = true

/-- Inference is complete for well-typed expressions: since every form carries enough
information to determine its own type, a type exists exactly when `infer` finds one. -/
public theorem Expression.wellTyped_iff_infer_isSome (td : TypeDecls) (ctx : Context)
    (e : Expression) : e.WellTyped td ctx ↔ (e.infer td ctx).isSome := by
  simp [Expression.WellTyped, Expression.check, Option.isSome_iff_exists]

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
public def Globals.types : Globals → Context
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

/-- Check a declaration: its body has to check against the declared result type under its own
parameters over the globals.

The parameters come first, so a parameter shadows a global of the same name.  `Env.lookup` resolves
a name the same way round, and that agreement is what `Eval.hasType` rests on. -/
public def FuncDecl.check (d : FuncDecl) (td : TypeDecls) (gs : Globals) : Bool :=
  d.body.check td (d.parameters ++ Globals.types gs) d.resultType

/-- `d`'s body agrees with the types `d` declares for its parameters and its result, given `td` and
`gs`. -/
public def FuncDecl.WellTyped (d : FuncDecl) (td : TypeDecls) (gs : Globals) : Prop :=
  d.check td gs = true

/-- `FuncDecl.check`'s body is not visible outside this module, so this is how a proof elsewhere
gets at what `WellTyped` says: inference on the body finds exactly the declared result type. -/
@[simp, grind =] public theorem FuncDecl.wellTyped_iff_infer_eq_some {d : FuncDecl} {td : TypeDecls}
    {gs : Globals} :
    d.WellTyped td gs ↔ d.body.infer td (d.parameters ++ Globals.types gs) = some d.resultType := by
  simp [FuncDecl.WellTyped, FuncDecl.check, Expression.check]

/-- Every declaration in `gs` checks, each under a context holding all of them.

Itself included — which is what lets a global call itself, and two globals call each other.  This
is a condition on syntax alone: no value occurs in it.  That is what keeps it provable at all.  A
value-level version would have to type each global's closure, which carries the globals table,
which would need typing again, and no inductive relation survives that regress.

Exposed, unlike the rest of this module's definitions: it is a specification rather than an
algorithm, there is nothing in it for an inversion principle to recover, and every consumer needs to
instantiate it at a name. -/
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

/-- Run the checker over a whole table.  Decides `Globals.WellTyped`, which `#guard` can report on
even where the kernel cannot reduce `Expression.infer`. -/
public def Globals.check (td : TypeDecls) (gs : Globals) : Bool := gs.all fun p => p.2.check td gs

/-- `Globals.check` is what it says it is.  It is the stronger of the two: it checks every entry,
where `Globals.WellTyped` only constrains the ones a lookup can reach. -/
public theorem Globals.wellTyped_of_check {td : TypeDecls} {gs : Globals}
    (h : Globals.check td gs = true) : Globals.WellTyped td gs :=
  Globals.wellTyped_of_forall fun p hp => List.all_eq_true.mp h p hp

/-! ## Programs

Checking a whole `Program`.  The tables it presents — `Program.globals`, `Program.typeDecls` and
the lookups through them — are in `LgtmDeepLean.Lang.TypeCheck.TypeDecls`, and the conditions under
which those lookups resolve every declaration are in `LgtmDeepLean.Lang.TypeCheck.Uniqueness`. -/

/-- Check a whole program: the types it declares are well formed, and every declaration checks
against the signatures of all of them, its own included, and against those types.

Well formed is `Program.FieldNamesUnique` and `Program.CtorNamesUnique`: a field or a constructor
declared twice is one the rest of the language cannot reach, so a declaration carrying one is
rejected here rather than left to mean less than it says.  Neither is a condition on any expression,
which is why they are checked once over the declarations instead of anywhere in `Expression.infer`.

The conditions across declarations are not part of this; see
`LgtmDeepLean.Lang.TypeCheck.Uniqueness`. -/
public def Program.check (p : Program) : Bool :=
  decide p.FieldNamesUnique && decide p.CtorNamesUnique && Globals.check p.typeDecls p.globals

/-- Every declaration in `p` checks, under `p`. -/
@[expose] public def Program.WellTyped (p : Program) : Prop :=
  Globals.WellTyped p.typeDecls p.globals

/-- `Program.check` is the stronger of the two, as `Globals.check` is: it also has the type
declarations to be well formed, which `Program.WellTyped` says nothing about. -/
public theorem Program.wellTyped_of_check {p : Program} (h : p.check = true) : p.WellTyped := by
  simp only [Program.check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact Globals.wellTyped_of_check h.2

/-- The other half of what `Program.check` decided: no structure declaration repeats a field name.
`Program.check`'s body is not visible outside this module, so this is how a proof gets at it. -/
public theorem Program.fieldNamesUnique_of_check {p : Program} (h : p.check = true) :
    p.FieldNamesUnique := by
  simp only [Program.check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

/-- And no inductive declaration repeats a constructor name. -/
public theorem Program.ctorNamesUnique_of_check {p : Program} (h : p.check = true) :
    p.CtorNamesUnique := by
  simp only [Program.check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

/-- Everything a well-typed program declares is well typed under it. -/
public theorem Program.wellTyped_decl {p : Program} (hp : p.WellTyped) (hu : p.NamesUnique)
    {d : FuncDecl} (hd : d ∈ p.funcDecls) : d.WellTyped p.typeDecls p.globals :=
  hp d.name d (Program.lookup_self hu hd)
