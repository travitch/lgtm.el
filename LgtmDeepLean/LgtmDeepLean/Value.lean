module

public import LgtmDeepLean.IR
public import LgtmDeepLean.TypeCheck
meta import LgtmDeepLean.IR
meta import LgtmDeepLean.TypeCheck

/-! # Values and environments

What an expression evaluates *to*, and what it evaluates *in*, together with what it means for
either to agree with the types `TypeCheck.lean` assigns.  Everything here is stated without
mentioning `Eval`: the evaluation relation is one consumer of this layer, but the notion of a value
having a type, and of an environment describing a context, stands on its own. -/

public inductive Value where
| int : Int → Value
| string : String → Value
| list : List Value → Value
/-- A function together with the environment it was written in: the bindings it captured and the
globals it was reached among, then the parameters and body of the `lam` itself.

The parameters are annotated the way `lam` annotates them, so a closure carries everything needed
to say what type it has.

The two halves of the environment are stored separately rather than as an `Env`, because an `Env`
holding `Value`s and a `Value` holding an `Env` would have to be declared in a `mutual` block, and
a structure declared there has neither definitional eta nor reducing projections.  `Env.closure`
is the way to build one of these from an environment, and `Env.HasType` is what says the two halves
belong together. -/
| closure : List (String × Value) → Globals → List (String × Ty) → Expression → Value

/-- What a name is bound to while an expression runs: the local bindings, innermost first, over the
globals every expression can see.

`bindings` is ordered, and `Env.lookup` reads the first binding of a name, so pushing onto the front
shadows what was there.

`globals` holds *declarations* rather than values, which is what makes globals recursive.  A table
of values would have to contain, for each global function, a closure that had captured the table —
a value that is its own descendant, which no inductive type has.  Resolving a global's name to its
closure is deferred to `Env.lookup` instead, where the table is to hand. -/
public structure Env where
  bindings : List (String × Value)
  globals : Globals

/-- The closure a `lam` reached in `env` evaluates to: the two halves of `env`, kept apart the way
`Value.closure` stores them. -/
@[expose] public def Env.closure (env : Env) (ps : List (String × Ty)) (body : Expression) :
    Value :=
  .closure env.bindings env.globals ps body

/-! The definitions a concrete evaluation computes with are exposed, the way `Program.lookup` and
its neighbours are: running `Eval` on an environment built out of them leaves goals like
`env.lookup "x" = some (.int 1)`, which are `rfl` only if the module the evaluation is written in
can see through every step of the way that environment was built. -/

/-- The environment a global's body runs in: no local bindings, and the same globals, so a global
can reach its siblings and itself. -/
@[expose] public def Globals.env (gs : Globals) : Env := ⟨[], gs⟩

@[simp] public theorem Globals.bindings_env (gs : Globals) : (Globals.env gs).bindings = [] := by
  simp [Globals.env]

@[simp] public theorem Globals.globals_env (gs : Globals) : (Globals.env gs).globals = gs := by
  simp [Globals.env]

/-- The value a global's name denotes: its body as a closure over the globals and nothing else.

Building this at each mention rather than once up front is what sidesteps the cyclic value a
recursive global would otherwise need. -/
@[expose] public def Globals.value (gs : Globals) (d : Decl) : Value :=
  (Globals.env gs).closure d.parameters d.body

/-- The value `x` is bound to, or `none` when it is unbound.

The local bindings are searched first, so a parameter shadows a global of the same name — the same
way round as `Decl.check`, which puts the parameters in front of `Globals.types`.  Keeping those two
orders together is what makes `Eval.hasType`'s variable case go through. -/
@[expose] public def Env.lookup (env : Env) (x : String) : Option Value :=
  match env.bindings.lookup x with
  | some v => some v
  | none => (env.globals.lookup x).map (Globals.value env.globals)

/-- The environment binding nothing and declaring nothing. -/
public instance : EmptyCollection Env := ⟨⟨[], []⟩⟩

@[simp] public theorem Env.bindings_empty : (∅ : Env).bindings = [] := by
  simp [EmptyCollection.emptyCollection]

@[simp] public theorem Env.globals_empty : (∅ : Env).globals = [] := by
  simp [EmptyCollection.emptyCollection]

/-- A name the bindings supply resolves to the value they give it, globals unconsulted. -/
public theorem Env.lookup_of_bindings {env : Env} {x : String} {v : Value}
    (h : env.bindings.lookup x = some v) : env.lookup x = some v := by
  simp [Env.lookup, h]

/-- A name the bindings do not supply falls through to the globals. -/
public theorem Env.lookup_of_globals {env : Env} {x : String}
    (h : env.bindings.lookup x = none) :
    env.lookup x = (env.globals.lookup x).map (Globals.value env.globals) := by
  simp [Env.lookup, h]

/-- The `Ty` a value's representation agrees with.

A list value is homogeneous: every element has the list's single element type.

A closure has a function type when its body checks against the result type under its parameters and
*some* context its captured environment agrees with.  That agreement is `Env.HasType`, but it cannot
be named here — `Env.HasType` is a definition, and it is defined in terms of `Value.HasType` — and it
cannot even be written out as it stands, because the kernel refuses a recursive occurrence under an
`∃`.  So the three halves of it are separated: the captured bindings and the context cover the same
names, and every value bound has the type promised for it.  `Value.hasType_closure_iff` puts them
back together and is the form to use.

Only the *local* bindings descend into `HasType` like that.  The globals the closure carries are
held to `Globals.WellTyped`, a condition on their syntax, precisely so that they do not: a global's
value is a closure over the globals, so typing one value-wise would ask for the same judgement
again, and this relation would have no least fixed point. -/
public inductive Value.HasType : Value → Ty → Prop where
| int (i : Int) : HasType (.int i) .int
| string (s : String) : HasType (.string s) .string
| list {vs : List Value} {t : Ty} : (∀ v ∈ vs, HasType v t) → HasType (.list vs) (.list t)
| closure {cbindings : List (String × Value)} {cglobals : Globals} {ps : Context}
    {body : Expression} {cctx : Context} {r : Ty} :
    Globals.WellTyped cglobals →
    (∀ x, (cctx.lookup x).isSome → (cbindings.lookup x).isSome) →
    (∀ x, (cbindings.lookup x).isSome → (cctx.lookup x).isSome) →
    (∀ x t v, cctx.lookup x = some t → cbindings.lookup x = some v → HasType v t) →
    body.infer (ps ++ cctx ++ Globals.types cglobals) = some r →
    HasType (.closure cbindings cglobals ps body) (.fn (ps.map Prod.snd) r)

/-- `env`'s globals all check, and its bindings are exactly the names `ctx` promises, at the types
`ctx` gives them.

This is the environment-level counterpart of `Value.HasType`: it is what makes a `varRef` safe to
evaluate, and it is the only thing `Eval.hasType` needs to know about an environment.

The domains have to match in *both* directions now that globals exist.  A binding the context has
not heard of would be read by `Env.lookup` in preference to a global of the same name, while
`Expression.infer` would have gone to the global for its type — so without the second clause a
stray binding could hand a `varRef` a value of the wrong type.

It is exposed, like `Globals.WellTyped`, because proofs elsewhere build one of these and take one
apart as the conjunction it is. -/
@[expose] public def Env.HasType (env : Env) (ctx : Context) : Prop :=
  Globals.WellTyped env.globals
    ∧ (∀ x, (env.bindings.lookup x).isSome → (ctx.lookup x).isSome)
    ∧ (∀ x t, ctx.lookup x = some t → ∃ v, env.bindings.lookup x = some v ∧ v.HasType t)

/-- What it takes for a closure to have a type, in terms of `Env.HasType`.

The context is existential: a closure's type says nothing about which names it captured, only that
whatever it captured was enough to type its body.

The two halves the closure stores are put back together here as the `Env` they came from, which is
what lets `Eval.hasType` hand `Env.HasType` straight to the induction hypothesis for the body. -/
@[simp] public theorem Value.hasType_closure_iff {cbindings : List (String × Value)}
    {cglobals : Globals} {ps : Context} {body : Expression} {t : Ty} :
    Value.HasType (.closure cbindings cglobals ps body) t ↔
      ∃ cctx r, Env.HasType ⟨cbindings, cglobals⟩ cctx
        ∧ body.infer (ps ++ cctx ++ Globals.types cglobals) = some r
        ∧ t = .fn (ps.map Prod.snd) r := by
  constructor
  · intro h
    cases h with
    | closure hgs hbinds hdom htypes hbody =>
        refine ⟨_, _, ⟨hgs, hdom, fun x t hx => ?_⟩, hbody, rfl⟩
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hbinds x (by simp [hx]))
        exact ⟨v, hv, htypes x t v hx hv⟩
  · rintro ⟨cctx, r, ⟨hgs, hdom, hval⟩, hbody, rfl⟩
    refine .closure hgs (fun x hx => ?_) hdom (fun x t v hx hv => ?_) hbody
    · obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hx
      obtain ⟨v, hv, -⟩ := hval x t ht
      simp [hv]
    · obtain ⟨v', hv', hty⟩ := hval x t hx
      grind

/-- A globals table that checks is an environment describing the empty context: it has no local
bindings for the context to disagree with. -/
public theorem Globals.hasType_env {gs : Globals} (h : Globals.WellTyped gs) :
    Env.HasType (Globals.env gs) [] :=
  ⟨by simpa [Globals.env] using h, by simp [Globals.env], by simp⟩

/-- `env` with each name in `ps` bound to the value in `vs` at the same position, in front of what
`env` had, so the new bindings shadow it.  The globals are carried through untouched.

`List.zip` stops at the shorter list, so this only describes a call once the two are known to be the
same length; `ArgsHaveType` is what supplies that. -/
@[expose] public def Env.extend (env : Env) (ps : Context) (vs : List Value) : Env :=
  { env with bindings := (ps.map Prod.fst).zip vs ++ env.bindings }

@[simp] public theorem Env.globals_extend (env : Env) (ps : Context) (vs : List Value) :
    (env.extend ps vs).globals = env.globals := by simp [Env.extend]

/-- `ArgsHaveType ps args`: `args` are values a function with parameters `ps` can be called with,
one argument per parameter and each of the type its parameter declares.

Walking the two lists together also pins the arity down: a call passing too few or too many
arguments has no such proof. -/
public inductive ArgsHaveType : Context → List Value → Prop where
| nil : ArgsHaveType [] []
| cons (x : String) : v.HasType t → ArgsHaveType ps args → ArgsHaveType ((x, t) :: ps) (v :: args)

/-- One well-typed binding on the front of the environment and its type on the front of the context
keeps the two in step.

Both domain clauses of `Env.HasType` are settled by the same case split: the new name is in both
lists or in neither. -/
public theorem Env.hasType_cons {env : Env} {ctx : Context} {x : String} {v : Value} {t : Ty}
    (hv : v.HasType t) (henv : Env.HasType env ctx) :
    Env.HasType ⟨(x, v) :: env.bindings, env.globals⟩ ((x, t) :: ctx) := by
  obtain ⟨hgs, hdom, hval⟩ := henv
  refine ⟨by simpa using hgs, fun y hy => ?_, fun y t' hy => ?_⟩ <;>
    simp only [List.lookup_cons] at hy ⊢ <;>
    split at hy
  · simp_all
  · simpa [show ¬ (y == x) = true by grind] using hdom y hy
  · exact ⟨v, by simp_all, by grind⟩
  · obtain ⟨v', hv', hty⟩ := hval y t' hy
    exact ⟨v', by simpa [show ¬ (y == x) = true by grind] using hv', hty⟩

/-- Binding well-typed arguments to their parameters in front of an environment gives an environment
the extended context describes.

The parameters shadow the captured environment on both sides at once — in the environment because
`Env.extend` puts them first, and in the context because they are appended on the left — which is
what keeps the two in step. -/
public theorem Env.hasType_extend {ps : Context} {vs : List Value} {env : Env} {ctx : Context}
    (h : ArgsHaveType ps vs) (henv : Env.HasType env ctx) :
    Env.HasType (env.extend ps vs) (ps ++ ctx) := by
  induction h with
  | nil => simpa [Env.extend] using henv
  | cons _ hv _ ih => simpa [Env.extend] using Env.hasType_cons hv ih

/-- The environment a call to `d` evaluates its body in: each parameter name bound to its
argument, over the globals and nothing else.

`Env.lookup` reads the first binding of a name, so a parameter repeated in `d.parameters` takes
the argument of its leftmost occurrence, and a parameter named like a global shadows it. -/
@[expose] public def Decl.callEnv (d : Decl) (gs : Globals) (args : List Value) : Env :=
  (Globals.env gs).extend d.parameters args

/-- Binding well-typed arguments to a declaration's parameters over its globals gives an environment
the parameter list describes.

`Decl.parameters` is a `Context`, so this is what lets a call use it as one: the types the
body was written against and the types the arguments arrive with are the same list. -/
public theorem Env.hasType_callEnv {d : Decl} {gs : Globals} {args : List Value}
    (hgs : Globals.WellTyped gs) (h : ArgsHaveType d.parameters args) :
    Env.HasType (d.callEnv gs args) d.parameters := by
  simpa [Decl.callEnv] using Env.hasType_extend h (Globals.hasType_env hgs)
