module

public import LgtmDeepLean.IR
meta import LgtmDeepLean.IR

/-- The types of the variables in scope, innermost binding first. -/
public abbrev Context := List (String × Ty)

/-- A name is looked up in the left half of an appended context first, so what is on the left
shadows what is on the right. -/
public theorem Context.lookup_append {ctx₁ ctx₂ : Context} {x : String} :
    (ctx₁ ++ ctx₂).lookup x =
      match ctx₁.lookup x with
      | some t => some t
      | none => ctx₂.lookup x := by
  induction ctx₁ with
  | nil => rfl
  | cons p ps ih =>
      obtain ⟨k, t⟩ := p
      by_cases h : x == k <;> simp [List.lookup_cons, h, ih]

mutual

/-- Infer the type of `e` under `ctx`, or `none` if `e` is ill typed.

Every form determines its own type: `lnil` carries the element type of the empty list it builds and
`lam` carries the types of its parameters, so inference never has to guess and needs no expected
type to work from.  `Expression.check` is therefore just this function plus a comparison. -/
public def Expression.infer (ctx : Context) : Expression → Option Ty
  | .lam ps body => do
    let r ← body.infer (ps ++ ctx)
    some (.fn (ps.map Prod.snd) r)
  | .app f args =>
    match f.infer ctx with
    | some (.fn ps r) => if Expression.inferList ctx args == some ps then some r else none
    | _ => none
  | .let_ x e body => do
    let t ← e.infer ctx
    body.infer ((x, t) :: ctx)
  | .varRef x => ctx.lookup x
  | .intLit _ => some .int
  | .plus l r | .minus l r =>
    if l.infer ctx == some .int && r.infer ctx == some .int then some .int else none
  | .stringLit _ => some .string
  | .lnil t => some (.list t)
  | .lcons hd tl => do
    let t ← hd.infer ctx
    guard (tl.infer ctx == some (.list t))
    some (.list t)
  | .listReverse l =>
    match l.infer ctx with
    | some (.list t) => some (.list t)
    | _ => none

/-- Infer the types of `es`, in order, or `none` if any one of them is ill typed.

This is mutual with `Expression.infer` because `app` holds a `List Expression`, which is how
`Expression.rec` offers the nesting: one motive for `Expression`, one for `List Expression`. -/
public def Expression.inferList (ctx : Context) : List Expression → Option (List Ty)
  | [] => some []
  | e :: es => do
    let t ← e.infer ctx
    let ts ← Expression.inferList ctx es
    some (t :: ts)

end

/-! Inversion principles for `infer`, one per syntactic form.

`infer`'s body is not visible outside this module, so a proof elsewhere cannot unfold it and has
to go through these instead.  They are `simp` lemmas, so a hypothesis `e.infer ctx = some t`
decomposes into premises about `e`'s subterms automatically. -/

@[simp, grind =] public theorem Expression.infer_varRef {ctx : Context} {x : String} :
    (Expression.varRef x).infer ctx = ctx.lookup x := by
  simp [Expression.infer]

@[simp, grind =] public theorem Expression.infer_intLit {ctx : Context} {i : Int} :
    (Expression.intLit i).infer ctx = some .int := by
  simp [Expression.infer]

@[simp, grind =] public theorem Expression.infer_stringLit {ctx : Context} {s : String} :
    (Expression.stringLit s).infer ctx = some .string := by
  simp [Expression.infer]

@[simp, grind =] public theorem Expression.infer_lnil {ctx : Context} {t : Ty} :
    (Expression.lnil t).infer ctx = some (.list t) := by
  simp [Expression.infer]

/-- A `plus` is typeable exactly when both operands are `int`s, and then it is an `int`. -/
@[simp, grind =] public theorem Expression.infer_plus_eq_some {ctx : Context} {l r : Expression} {t : Ty} :
    (Expression.plus l r).infer ctx = some t ↔
      l.infer ctx = some .int ∧ r.infer ctx = some .int ∧ t = .int := by
  simp [Expression.infer]
  grind

/-- A `minus` is typeable exactly when both operands are `int`s, and then it is an `int`. -/
@[simp, grind =] public theorem Expression.infer_minus_eq_some {ctx : Context} {l r : Expression} {t : Ty} :
    (Expression.minus l r).infer ctx = some t ↔
      l.infer ctx = some .int ∧ r.infer ctx = some .int ∧ t = .int := by
  simp [Expression.infer]
  grind

/-- An `lcons` is typeable exactly when its tail is a list of its head's type.

This is what makes the values `Eval` builds homogeneous: the element type is read off the head
and then *required* of the tail, so one `Ty` covers every element. -/
@[simp, grind =] public theorem Expression.infer_lcons_eq_some {ctx : Context} {hd tl : Expression}
    {t : Ty} :
    (Expression.lcons hd tl).infer ctx = some t ↔
      ∃ t', hd.infer ctx = some t' ∧ tl.infer ctx = some (.list t') ∧ t = .list t' := by
  simp [Expression.infer, Option.bind_eq_some_iff, guard]
  grind

/-- A `listReverse` is typeable exactly when its operand is a list, and then it has that same list
type.

Reversing preserves both the length and the element type, so the operand's type is also the
result's: unlike `lcons`, this form introduces no new type structure. -/
@[simp, grind =] public theorem Expression.infer_listReverse_eq_some {ctx : Context}
    {l : Expression} {t : Ty} :
    (Expression.listReverse l).infer ctx = some t ↔
      ∃ t', l.infer ctx = some (.list t') ∧ t = .list t' := by
  simp only [Expression.infer]
  split <;> grind

/-- A `lam` is typeable exactly when its body is, under its parameters extended with the enclosing
context, and then it is a function from the parameters' types to the body's.

Parameters go on the front of the context, so they shadow same-named bindings from outside, and — as
in `Decl.callEnv` — a name repeated in the parameter list refers to its leftmost occurrence. -/
@[simp, grind =] public theorem Expression.infer_lam_eq_some {ctx : Context}
    {ps : List (String × Ty)} {body : Expression} {t : Ty} :
    (Expression.lam ps body).infer ctx = some t ↔
      ∃ r, body.infer (ps ++ ctx) = some r ∧ t = .fn (ps.map Prod.snd) r := by
  simp [Expression.infer, Option.bind_eq_some_iff]
  grind

/-- An `app` is typeable exactly when its function's type is a function type whose parameter types
are the types of the arguments, in order, and then it is that function type's result.

Because `Ty.fn` records all the parameters at once, arity is part of that one comparison: a call
passing too few arguments is ill typed rather than partially applied. -/
@[simp, grind =] public theorem Expression.infer_app_eq_some {ctx : Context} {f : Expression}
    {args : List Expression} {t : Ty} :
    (Expression.app f args).infer ctx = some t ↔
      ∃ ps, f.infer ctx = some (.fn ps t) ∧ Expression.inferList ctx args = some ps := by
  simp only [Expression.infer]
  split <;> grind

/-- A `let_` is typeable exactly when the expression it binds is and its body is under that name at
that type, and then it has the body's type.

The bound expression's type is inferred rather than annotated, which is why `let_` carries no `Ty`:
there is nothing for the writer to declare that inference does not already determine.  The name goes
on the front of the context, so it shadows an outer binding of the same name, and the bound
expression is typed *before* it is added, so `let x = x` still refers to the outer `x`. -/
@[simp, grind =] public theorem Expression.infer_let_eq_some {ctx : Context} {x : String}
    {e body : Expression} {t : Ty} :
    (Expression.let_ x e body).infer ctx = some t ↔
      ∃ t', e.infer ctx = some t' ∧ body.infer ((x, t') :: ctx) = some t := by
  simp [Expression.infer, Option.bind_eq_some_iff]

/-! Inversion principles for `inferList`.  Together these say what it computes: the argument types
in order, and `none` as soon as one argument has no type. -/

@[simp, grind =] public theorem Expression.inferList_nil {ctx : Context} :
    Expression.inferList ctx [] = some [] := by
  simp [Expression.inferList]

@[simp, grind =] public theorem Expression.inferList_cons_eq_some {ctx : Context} {e : Expression}
    {es : List Expression} {ts : List Ty} :
    Expression.inferList ctx (e :: es) = some ts ↔
      ∃ t ts', e.infer ctx = some t ∧ Expression.inferList ctx es = some ts' ∧ ts = t :: ts' := by
  simp [Expression.inferList, Option.bind_eq_some_iff]
  grind

/-- Check `e` against the expected type `ty` under `ctx`. -/
public def Expression.check (ctx : Context) (e : Expression) (ty : Ty) : Bool :=
  e.infer ctx == some ty

/-- `e` is well typed under `ctx` at some type. -/
public def Expression.WellTyped (ctx : Context) (e : Expression) : Prop :=
  ∃ t, e.check ctx t = true

/-- Inference is complete for well-typed expressions: since every form carries enough
information to determine its own type, a type exists exactly when `infer` finds one. -/
public theorem Expression.wellTyped_iff_infer_isSome (ctx : Context) (e : Expression) :
    e.WellTyped ctx ↔ (e.infer ctx).isSome := by
  simp [Expression.WellTyped, Expression.check, Option.isSome_iff_exists]

/-! ## Globals

The declarations a body may mention besides its own parameters.  A `Globals` is a table of
*declarations*, not of values: every global is a function, and a global variable is a function of
no arguments, written `g()`.

One mechanism covers both because recursion needs it to.  A table of values would have to be built
before anything could mention it, so a declaration could never refer to itself or to one defined
after it; a table of declarations is just syntax, and a body can be checked against a context
listing every entry including its own. -/

/-- The declarations in scope everywhere, each under the name it is referred to by. -/
public abbrev Globals := List (String × Decl)

/-- Key each declaration by the name it declares. -/
@[expose] public def Globals.ofDecls (ds : List Decl) : Globals := ds.map fun d => (d.name, d)

/-- The type a declaration has where its name is mentioned: a function from its parameters' types
to its result type.

A declaration of no parameters gets `.fn [] t` rather than `t`, which is what makes a global
variable a call. -/
@[expose] public def Decl.ty (d : Decl) : Ty := .fn (d.parameters.map Prod.snd) d.resultType

/-- The context `gs` supplies: every global's name at the type of the declaration stored for it. -/
public def Globals.types : Globals → Context
  | [] => []
  | (x, d) :: gs => (x, d.ty) :: Globals.types gs

@[simp] public theorem Globals.types_nil : Globals.types [] = [] := by simp [Globals.types]

@[simp] public theorem Globals.types_cons (x : String) (d : Decl) (gs : Globals) :
    Globals.types ((x, d) :: gs) = (x, d.ty) :: Globals.types gs := by simp [Globals.types]

/-- `Globals.types` is `Decl.ty` under the lookup, which is how a proof gets from the type a name
was inferred at back to the declaration that gave it. -/
@[simp, grind =] public theorem Globals.lookup_types {gs : Globals} {x : String} :
    (Globals.types gs).lookup x = (gs.lookup x).map Decl.ty := by
  induction gs with
  | nil => rfl
  | cons p gs ih =>
      obtain ⟨k, d⟩ := p
      by_cases h : x == k <;> simp [Globals.types, List.lookup_cons, h, ih]

/-- Check a declaration: its body has to check against the declared result type under its own
parameters over the globals.

The parameters come first, so a parameter shadows a global of the same name.  `Env.lookup` resolves
a name the same way round, and that agreement is what `Eval.hasType` rests on. -/
public def Decl.check (d : Decl) (gs : Globals) : Bool :=
  d.body.check (d.parameters ++ Globals.types gs) d.resultType

/-- `d`'s body agrees with the types `d` declares for its parameters and its result, given `gs`. -/
public def Decl.WellTyped (d : Decl) (gs : Globals) : Prop :=
  d.check gs = true

/-- `Decl.check`'s body is not visible outside this module, so this is how a proof elsewhere gets
at what `WellTyped` says: inference on the body finds exactly the declared result type. -/
@[simp, grind =] public theorem Decl.wellTyped_iff_infer_eq_some {d : Decl} {gs : Globals} :
    d.WellTyped gs ↔ d.body.infer (d.parameters ++ Globals.types gs) = some d.resultType := by
  simp [Decl.WellTyped, Decl.check, Expression.check]

/-- Every declaration in `gs` checks, each under a context holding all of them.

Itself included — which is what lets a global call itself, and two globals call each other.  This
is a condition on syntax alone: no value occurs in it.  That is what keeps it provable at all.  A
value-level version would have to type each global's closure, which carries the globals table,
which would need typing again, and no inductive relation survives that regress.

Exposed, unlike the rest of this module's definitions: it is a specification rather than an
algorithm, there is nothing in it for an inversion principle to recover, and every consumer needs to
instantiate it at a name. -/
@[expose] public def Globals.WellTyped (gs : Globals) : Prop :=
  ∀ x d, gs.lookup x = some d → d.WellTyped gs

/-- A program with no globals has nothing to check. -/
public theorem Globals.wellTyped_nil : Globals.WellTyped [] := by
  intro x d hx; simp at hx

/-- A lookup only ever hands back an entry the table contains. -/
public theorem Globals.mem_of_lookup {gs : Globals} {x : String} {d : Decl}
    (h : gs.lookup x = some d) : (x, d) ∈ gs := by
  induction gs with
  | nil => simp at h
  | cons p gs ih =>
      obtain ⟨k, e⟩ := p
      rw [List.lookup_cons] at h
      split at h
      · obtain rfl : x = k := by grind
        obtain rfl : d = e := by grind
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)

/-- A table checks if each of its entries does.

Stated over membership rather than lookup because that is what a table written out as a literal can
be discharged against, one entry at a time. -/
public theorem Globals.wellTyped_of_forall {gs : Globals}
    (h : ∀ p ∈ gs, Decl.WellTyped p.2 gs) : Globals.WellTyped gs :=
  fun x d hx => h (x, d) (Globals.mem_of_lookup hx)

/-- Run the checker over a whole table.  Decides `Globals.WellTyped`, which `#guard` can report on
even where the kernel cannot reduce `Expression.infer`. -/
public def Globals.check (gs : Globals) : Bool := gs.all fun p => p.2.check gs

/-- `Globals.check` is what it says it is.  It is the stronger of the two: it checks every entry,
where `Globals.WellTyped` only constrains the ones a lookup can reach. -/
public theorem Globals.wellTyped_of_check {gs : Globals} (h : Globals.check gs = true) :
    Globals.WellTyped gs :=
  Globals.wellTyped_of_forall fun p hp => List.all_eq_true.mp h p hp

@[simp] public theorem Globals.ofDecls_nil : Globals.ofDecls [] = [] := by simp [Globals.ofDecls]

@[simp] public theorem Globals.ofDecls_cons (d : Decl) (ds : List Decl) :
    Globals.ofDecls (d :: ds) = (d.name, d) :: Globals.ofDecls ds := by simp [Globals.ofDecls]

/-- With no repeated names, `Globals.ofDecls` resolves every declaration to itself. -/
public theorem Globals.lookup_ofDecls_self {ds : List Decl} (hu : (ds.map Decl.name).Nodup)
    {d : Decl} (hd : d ∈ ds) : (Globals.ofDecls ds).lookup d.name = some d := by
  induction ds with
  | nil => simp at hd
  | cons e es ih =>
      rw [List.map_cons, List.nodup_cons] at hu
      simp only [Globals.ofDecls_cons, List.lookup_cons]
      rcases List.mem_cons.mp hd with rfl | hd'
      · simp
      · have hne : ¬ (d.name == e.name) = true := fun h =>
          hu.1 (List.mem_map.mpr ⟨d, hd', by grind⟩)
        simpa [hne] using ih hu.2 hd'

/-! ## Programs

A `Program` is the source-level artifact — a file's worth of declarations — where a `Globals` is the
table those declarations are checked and run against.  `Program.globals` is the bridge.

The definitions below are exposed, unlike the rest of this module's: each is a projection or an
alias with nothing an inversion principle could recover.  `Program.check` is not, for the same
reason `Globals.check` is not — it runs `Expression.infer`, which stays hidden. -/

/-- The globals table `p` presents to its own bodies: each declaration under the name it declares.

Derived rather than stored, so a declaration can never be filed under a name other than its own. -/
@[expose] public def Program.globals (p : Program) : Globals := Globals.ofDecls p.decls

/-- The declaration `x` names in `p`, or `none` if it names nothing. -/
@[expose] public def Program.lookup (p : Program) (x : String) : Option Decl := p.globals.lookup x

/-- Check a whole program: every declaration against the signatures of all of them, its own
included. -/
public def Program.check (p : Program) : Bool := Globals.check p.globals

/-- Every declaration in `p` checks, under `p`. -/
@[expose] public def Program.WellTyped (p : Program) : Prop := Globals.WellTyped p.globals

public theorem Program.wellTyped_of_check {p : Program} (h : p.check = true) : p.WellTyped :=
  Globals.wellTyped_of_check h

/-- No two declarations share a name.

`Program.lookup` takes the leftmost of a repeated name, so without this a second declaration of a
name already used is dead: `Program.check` still checks it, but nothing can call it.  Soundness does
not need this — a lookup is deterministic either way — but `Program.lookup_self` does, and so does
reading a program as "these declarations" rather than "these declarations, some of them shadowed". -/
@[expose] public def Program.NamesUnique (p : Program) : Prop := (p.decls.map Decl.name).Nodup

public instance (p : Program) : Decidable p.NamesUnique :=
  inferInstanceAs (Decidable (p.decls.map Decl.name).Nodup)

/-- With no repeated names, every declaration in the program is the one its own name resolves to.

This is what turns "`d` is one of `p`'s declarations" into "`d` is callable", which is what carrying
soundness from `Program.WellTyped` to a particular declaration needs. -/
public theorem Program.lookup_self {p : Program} (hu : p.NamesUnique) {d : Decl}
    (hd : d ∈ p.decls) : p.lookup d.name = some d :=
  Globals.lookup_ofDecls_self hu hd

/-- Everything a well-typed program declares is well typed under it. -/
public theorem Program.wellTyped_decl {p : Program} (hp : p.WellTyped) (hu : p.NamesUnique)
    {d : Decl} (hd : d ∈ p.decls) : d.WellTyped p.globals :=
  hp d.name d (Program.lookup_self hu hd)

section Tests

private def ctx : Context :=
  [("xs", .list .int), ("n", .int), ("s", .string), ("f", .fn [.int, .string] .int)]

-- Inference determines the type of every form.
#guard (Expression.intLit 3).infer ctx == some .int
#guard (Expression.stringLit "hi").infer ctx == some .string
#guard (Expression.varRef "n").infer ctx == some .int
#guard (Expression.varRef "s").infer ctx == some .string
#guard (Expression.varRef "xs").infer ctx == some (.list .int)
#guard (Expression.varRef "f").infer ctx == some (.fn [.int, .string] .int)
#guard (Expression.varRef "nope").infer ctx == none
#guard (Expression.plus (.varRef "n") (.intLit 1)).infer ctx == some .int
#guard (Expression.minus (.intLit 1) (.varRef "xs")).infer ctx == none

-- Arithmetic is on `int`s only: a string operand is rejected on either side.
#guard (Expression.plus (.stringLit "a") (.stringLit "b")).infer ctx == none
#guard (Expression.plus (.varRef "n") (.stringLit "b")).infer ctx == none
#guard (Expression.minus (.stringLit "a") (.varRef "n")).infer ctx == none

-- An empty list takes its type from its annotation, not from its context.
#guard (Expression.lnil .int).infer ctx == some (.list .int)
#guard (Expression.lnil (.list .int)).infer ctx == some (.list (.list .int))

-- A non-empty list takes its element type from its head, and its tail has to agree.
#guard (Expression.lcons (.intLit 1) (.lnil .int)).infer ctx == some (.list .int)
#guard (Expression.lcons (.intLit 1) (.varRef "xs")).infer ctx == some (.list .int)
#guard (Expression.lcons (.varRef "xs") (.lnil (.list .int))).infer ctx == some (.list (.list .int))
#guard (Expression.lcons (.intLit 1) (.intLit 2)).infer ctx == none
#guard (Expression.lcons (.intLit 1) (.lnil (.list .int))).infer ctx == none
#guard (Expression.lcons (.varRef "xs") (.varRef "xs")).infer ctx == none

-- Lists are homogeneous across the new type too, so a mixed list has no type.
#guard (Expression.lcons (.stringLit "a") (.lnil .string)).infer ctx == some (.list .string)
#guard (Expression.lcons (.stringLit "a") (.lnil .int)).infer ctx == none
#guard (Expression.lcons (.intLit 1) (.lnil .string)).infer ctx == none
#guard (Expression.lcons (.stringLit "a") (.varRef "xs")).infer ctx == none

-- A list of empty lists needs no expected type to be inferred, only agreeing annotations.
#guard (Expression.lcons (.lnil .int) (.lnil (.list .int))).infer ctx == some (.list (.list .int))
#guard (Expression.lcons (.lnil .int) (.lnil .int)).infer ctx == none

-- Reversing a list keeps its type, whatever the element type is.
#guard (Expression.listReverse (.varRef "xs")).infer ctx == some (.list .int)
#guard (Expression.listReverse (.lnil .string)).infer ctx == some (.list .string)
#guard (Expression.listReverse (.lcons (.intLit 1) (.lnil .int))).infer ctx == some (.list .int)
#guard (Expression.listReverse (.lnil (.list .int))).infer ctx == some (.list (.list .int))

-- Only a list can be reversed, so a non-list operand is ill typed rather than passed through.
#guard (Expression.listReverse (.intLit 1)).infer ctx == none
#guard (Expression.listReverse (.stringLit "a")).infer ctx == none
#guard (Expression.listReverse (.varRef "n")).infer ctx == none
#guard (Expression.listReverse (.varRef "f")).infer ctx == none

-- An ill-typed operand makes the whole reversal ill typed.
#guard (Expression.listReverse (.varRef "nope")).infer ctx == none
#guard (Expression.listReverse (.lcons (.intLit 1) (.lnil .string))).infer ctx == none

-- Reversals nest, since each one gives back a list.
#guard (Expression.listReverse (.listReverse (.varRef "xs"))).infer ctx == some (.list .int)
#guard (Expression.listReverse (.listReverse (.intLit 1))).infer ctx == none

-- A `lam` takes its parameter types from its annotation and its result type from its body.
#guard (Expression.lam [("x", .int)] (.varRef "x")).infer ctx == some (.fn [.int] .int)
#guard (Expression.lam [("x", .int), ("y", .string)] (.varRef "y")).infer ctx
  == some (.fn [.int, .string] .string)
#guard (Expression.lam [] (.intLit 1)).infer ctx == some (.fn [] .int)
#guard (Expression.lam [("x", .int)] (.varRef "nope")).infer ctx == none
#guard (Expression.lam [("x", .string)] (.plus (.varRef "x") (.intLit 1))).infer ctx == none

-- A body sees the enclosing context as well as the parameters, and the parameters shadow it.
#guard (Expression.lam [("x", .int)] (.plus (.varRef "x") (.varRef "n"))).infer ctx
  == some (.fn [.int] .int)
#guard (Expression.lam [("n", .string)] (.varRef "n")).infer ctx == some (.fn [.string] .string)
#guard (Expression.lam [("x", .int), ("x", .string)] (.varRef "x")).infer ctx
  == some (.fn [.int, .string] .int)

-- Function types are types like any other: a `lam` can return one, and a list can hold them.
#guard (Expression.lam [("x", .int)] (.lam [("y", .string)] (.varRef "x"))).infer ctx
  == some (.fn [.int] (.fn [.string] .int))
#guard (Expression.lcons (.varRef "f") (.lnil (.fn [.int, .string] .int))).infer ctx
  == some (.list (.fn [.int, .string] .int))
#guard (Expression.lcons (.varRef "f") (.lnil (.fn [.int] .int))).infer ctx == none

-- An `app` needs a function, and arguments whose types are the parameter types in order.
#guard (Expression.app (.varRef "f") [.intLit 1, .stringLit "a"]).infer ctx == some .int
#guard (Expression.app (.lam [("x", .int)] (.plus (.varRef "x") (.intLit 1))) [.intLit 2]).infer ctx
  == some .int
#guard (Expression.app (.lam [] (.intLit 1)) []).infer ctx == some .int
#guard (Expression.app (.varRef "f") [.stringLit "a", .intLit 1]).infer ctx == none
#guard (Expression.app (.varRef "f") [.varRef "nope", .stringLit "a"]).infer ctx == none
#guard (Expression.app (.varRef "n") [.intLit 1]).infer ctx == none
#guard (Expression.app (.lnil .int) []).infer ctx == none

-- Arity is part of the function type, so a call with the wrong number of arguments is ill typed
-- rather than partially applied.
#guard (Expression.app (.varRef "f") [.intLit 1]).infer ctx == none
#guard (Expression.app (.varRef "f") []).infer ctx == none
#guard (Expression.app (.varRef "f") [.intLit 1, .stringLit "a", .intLit 2]).infer ctx == none

-- Applying a function that returns a function gives the inner function type, which can then be
-- applied in turn.
#guard (Expression.app (.lam [("x", .int)] (.lam [("y", .string)] (.varRef "x"))) [.intLit 1]).infer
  ctx == some (.fn [.string] .int)
#guard (Expression.app (.app (.lam [("x", .int)] (.lam [("y", .string)] (.varRef "x"))) [.intLit 1])
  [.stringLit "a"]).infer ctx == some .int

-- A `let_` gives its body's type, with the bound name at the type inferred for what it binds.
#guard (Expression.let_ "x" (.intLit 1) (.plus (.varRef "x") (.intLit 2))).infer ctx == some .int
#guard (Expression.let_ "x" (.stringLit "a") (.varRef "x")).infer ctx == some .string
#guard (Expression.let_ "x" (.varRef "xs") (.varRef "x")).infer ctx == some (.list .int)
#guard (Expression.let_ "g" (.lam [("y", .int)] (.varRef "y"))
  (.app (.varRef "g") [.intLit 1])).infer ctx == some .int

-- An ill-typed expression on either side makes the whole `let_` ill typed.
#guard (Expression.let_ "x" (.varRef "nope") (.intLit 1)).infer ctx == none
#guard (Expression.let_ "x" (.intLit 1) (.plus (.varRef "x") (.stringLit "a"))).infer ctx == none
#guard (Expression.let_ "x" (.intLit 1) (.varRef "nope")).infer ctx == none

-- The name is added after the expression it binds is typed, so a `let_` is not recursive: the bound
-- expression sees the enclosing context only.
#guard (Expression.let_ "x" (.varRef "x") (.varRef "x")).infer ctx == none
#guard (Expression.let_ "n" (.plus (.varRef "n") (.intLit 1)) (.varRef "n")).infer ctx == some .int

-- The binding shadows an enclosing one of the same name, inner `let_`s included.
#guard (Expression.let_ "n" (.stringLit "a") (.varRef "n")).infer ctx == some .string
#guard (Expression.let_ "n" (.stringLit "a") (.plus (.varRef "n") (.intLit 1))).infer ctx == none
#guard (Expression.let_ "x" (.intLit 1) (.let_ "x" (.stringLit "a") (.varRef "x"))).infer ctx
  == some .string

-- `let_`s nest, and a later one sees what an earlier one bound.
#guard (Expression.let_ "x" (.intLit 1)
  (.let_ "y" (.plus (.varRef "x") (.intLit 1)) (.plus (.varRef "x") (.varRef "y")))).infer ctx
  == some .int

-- A `lam` body sees a `let_` from outside it, and a `let_` body sees the parameters.
#guard (Expression.let_ "x" (.intLit 1)
  (.lam [("y", .int)] (.plus (.varRef "x") (.varRef "y")))).infer ctx == some (.fn [.int] .int)
#guard (Expression.lam [("y", .int)]
  (.let_ "x" (.varRef "y") (.plus (.varRef "x") (.varRef "y")))).infer ctx == some (.fn [.int] .int)

-- Checking agrees with inference.
#guard (Expression.lnil .int).check ctx (.list .int)
#guard !(Expression.lnil .int).check ctx .int
#guard (Expression.plus (.varRef "n") (.intLit 1)).check ctx .int
#guard !(Expression.plus (.varRef "n") (.intLit 1)).check ctx (.list .int)
#guard !(Expression.plus (.varRef "n") (.lnil .int)).check ctx .int
#guard (Expression.stringLit "hi").check ctx .string
#guard !(Expression.stringLit "hi").check ctx .int
#guard (Expression.lam [("x", .int)] (.varRef "x")).check ctx (.fn [.int] .int)
#guard !(Expression.lam [("x", .int)] (.varRef "x")).check ctx (.fn [.string] .string)
#guard !(Expression.lam [("x", .int)] (.varRef "x")).check ctx .int

/-- `fun (x : int) (y : int) => x + (y - 1)` -/
private def addPred : Decl where
  docstring := "Add `x` to one less than `y`."
  name := "add-pred"
  parameters := [("x", .int), ("y", .int)]
  body := .plus (.varRef "x") (.minus (.varRef "y") (.intLit 1))
  resultType := .int

-- A declaration checks when its body agrees with the result type it declares.
#guard addPred.check []
#guard !({ addPred with resultType := .list .int } : Decl).check []

-- The parameter list is all the body has to work with, and it is checked at the types it gives.
#guard !({ addPred with parameters := [("x", .int)] } : Decl).check []
#guard !({ addPred with parameters := [("x", .int), ("y", .list .int)] } : Decl).check []

/-- `fun (s : string) => ["!", s]` -/
private def bang : Decl where
  docstring := "Put `s` after an exclamation mark."
  name := "bang"
  parameters := [("s", .string)]
  body := .lcons (.stringLit "!") (.lcons (.varRef "s") (.lnil .string))
  resultType := .list .string

#guard bang.check []
#guard !({ bang with resultType := .list .int } : Decl).check []
#guard !({ bang with parameters := [("s", .int)] } : Decl).check []

/-- `fun (g : (int) -> int) (x : int) => g(x)` -/
private def applyTo : Decl where
  docstring := "Call `g` on `x`."
  name := "apply-to"
  parameters := [("g", .fn [.int] .int), ("x", .int)]
  body := .app (.varRef "g") [.varRef "x"]
  resultType := .int

-- A parameter of function type is callable, at the arity and types its type gives.
#guard applyTo.check []
#guard !({ applyTo with parameters := [("g", .fn [.string] .int), ("x", .int)] } : Decl).check []
#guard !({ applyTo with parameters := [("g", .fn [.int, .int] .int), ("x", .int)] } : Decl).check []
#guard !({ applyTo with resultType := .string } : Decl).check []

/-- `fun (n : int) => fun (m : int) => n + m` -/
private def adder : Decl where
  docstring := "Build a function that adds `n` to its argument."
  name := "adder"
  parameters := [("n", .int)]
  body := .lam [("m", .int)] (.plus (.varRef "n") (.varRef "m"))
  resultType := .fn [.int] .int

-- A declaration can return a function, and its result type is checked like any other.
#guard adder.check []
#guard !({ adder with resultType := .int } : Decl).check []
#guard !({ adder with resultType := .fn [.string] .int } : Decl).check []

end Tests
