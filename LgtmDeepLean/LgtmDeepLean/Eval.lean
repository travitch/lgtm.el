module

public import LgtmDeepLean.IR
public import LgtmDeepLean.TypeCheck
meta import LgtmDeepLean.IR
meta import LgtmDeepLean.TypeCheck
import LgtmDeepLean.Syntax

mutual

public inductive Value where
| int : Int → Value
| string : String → Value
| list : List Value → Value
/-- A function together with the environment it was written in.

The parameters are annotated the way `lam` annotates them, so a closure carries everything needed
to say what type it has. -/
| closure : Env → List (String × Ty) → Expression → Value

/-- What a name is bound to while an expression runs: the local bindings, innermost first, over the
globals every expression can see.

`bindings` is ordered, and `Env.lookup` reads the first binding of a name, so pushing onto the front
shadows what was there.

`globals` holds *declarations* rather than values, which is what makes globals recursive.  A table
of values would have to contain, for each global function, a closure that had captured the table —
a value that is its own descendant, which no inductive type has.  Resolving a global's name to its
closure is deferred to `Env.lookup` instead, where the table is to hand.

The structure is mutual with `Value` because a closure captures one. -/
public structure Env where
  bindings : List (String × Value)
  globals : Globals

end

/-! Being declared in a `mutual` block costs `Env` the definitional eta and projection reduction a
plain structure would have, so the steps every proof below takes through `Env.mk` — projecting out
of it and rebuilding it — have to be lemmas. -/

@[simp] public theorem Env.bindings_mk (bs : List (String × Value)) (gs : Globals) :
    (Env.mk bs gs).bindings = bs := by simp

@[simp] public theorem Env.globals_mk (bs : List (String × Value)) (gs : Globals) :
    (Env.mk bs gs).globals = gs := by simp

@[simp] public theorem Env.mk_bindings (env : Env) : Env.mk env.bindings env.globals = env := by
  cases env; rfl

/-- The environment a global's body runs in: no local bindings, and the same globals, so a global
can reach its siblings and itself. -/
public def Globals.env (gs : Globals) : Env := ⟨[], gs⟩

@[simp] public theorem Globals.bindings_env (gs : Globals) : (Globals.env gs).bindings = [] := by
  simp [Globals.env]

@[simp] public theorem Globals.globals_env (gs : Globals) : (Globals.env gs).globals = gs := by
  simp [Globals.env]

/-- The value a global's name denotes: its body as a closure over the globals and nothing else.

Building this at each mention rather than once up front is what sidesteps the cyclic value a
recursive global would otherwise need. -/
public def Globals.value (gs : Globals) (d : Decl) : Value :=
  .closure (Globals.env gs) d.parameters d.body

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
| closure {cenv : Env} {ps : Context} {body : Expression} {cctx : Context} {r : Ty} :
    Globals.WellTyped cenv.globals →
    (∀ x, (cctx.lookup x).isSome → (cenv.bindings.lookup x).isSome) →
    (∀ x, (cenv.bindings.lookup x).isSome → (cctx.lookup x).isSome) →
    (∀ x t v, cctx.lookup x = some t → cenv.bindings.lookup x = some v → HasType v t) →
    body.infer (ps ++ cctx ++ Globals.types cenv.globals) = some r →
    HasType (.closure cenv ps body) (.fn (ps.map Prod.snd) r)

/-- `env`'s globals all check, and its bindings are exactly the names `ctx` promises, at the types
`ctx` gives them.

This is the environment-level counterpart of `Value.HasType`: it is what makes a `varRef` safe to
evaluate, and it is the only thing `Eval.hasType` needs to know about an environment.

The domains have to match in *both* directions now that globals exist.  A binding the context has
not heard of would be read by `Env.lookup` in preference to a global of the same name, while
`Expression.infer` would have gone to the global for its type — so without the second clause a
stray binding could hand a `varRef` a value of the wrong type. -/
public def Env.HasType (env : Env) (ctx : Context) : Prop :=
  Globals.WellTyped env.globals
    ∧ (∀ x, (env.bindings.lookup x).isSome → (ctx.lookup x).isSome)
    ∧ (∀ x t, ctx.lookup x = some t → ∃ v, env.bindings.lookup x = some v ∧ v.HasType t)

/-- What it takes for a closure to have a type, in terms of `Env.HasType`.

The context is existential: a closure's type says nothing about which names it captured, only that
whatever it captured was enough to type its body. -/
@[simp] public theorem Value.hasType_closure_iff {cenv : Env} {ps : Context} {body : Expression}
    {t : Ty} :
    Value.HasType (.closure cenv ps body) t ↔
      ∃ cctx r, Env.HasType cenv cctx
        ∧ body.infer (ps ++ cctx ++ Globals.types cenv.globals) = some r
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
public def Env.extend (env : Env) (ps : Context) (vs : List Value) : Env :=
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

/-- `env` is an index rather than a parameter because `EApp` evaluates a body in the environment its
closure captured, not in the one the call was made from. -/
public inductive Eval : Env → Expression → Value → Prop where
/-- A `lam` evaluates to itself plus the environment it was reached in; nothing in its body runs
until it is applied. -/
| ELam (ps : List (String × Ty)) (body : Expression) : Eval env (.lam ps body) (.closure env ps body)
/-- A call evaluates its function and its arguments, then the body in the closure's environment
extended with the parameters.

The arguments are related to their values pairwise rather than by a list-evaluation relation of
their own, which keeps `Eval` a single inductive and so keeps `induction` available on it — the same
trade `Value.HasType.list` makes.  `args.length = vs.length` is what makes that pairing total, since
`List.zip` would otherwise let a value appear that no argument produced.

As in `Decl.Apply`, `ArgsHaveType` is what makes a call with the wrong arguments stuck rather than
junk, and it pins the arity that `Env.extend` needs. -/
| EApp (f : Expression) (args : List Expression) :
    Eval env f (.closure cenv ps body) →
    args.length = vs.length → (∀ p ∈ args.zip vs, Eval env p.1 p.2) →
    ArgsHaveType ps vs →
    Eval (Env.extend cenv ps vs) body v →
    Eval env (.app f args) v
| EVarRef (x : String) : env.lookup x = some v → Eval env (.varRef x) v
| EIntLit (i : Int) : Eval env (.intLit i) (.int i)
| EPlus (e₁ : Expression) (e₂ : Expression) : Eval env e₁ (.int n₁) → Eval env e₂ (.int n₂) → Eval env (.plus e₁ e₂) (.int (n₁ + n₂))
| EMinus (e₁ : Expression) (e₂ : Expression) : Eval env e₁ (.int n₁) → Eval env e₂ (.int n₂) → Eval env (.minus e₁ e₂) (.int (n₁ - n₂))
| EStringLit (s : String) : Eval env (.stringLit s) (.string s)
| ENil (ty : Ty) : Eval env (.lnil ty) (.list [])
| ECons (e₁ : Expression) (e₂ : Expression) : Eval env e₁ v → Eval env e₂ (.list vs) → Eval env (.lcons e₁ e₂) (.list (v :: vs))
| EListReverse (e : Expression) : Eval env e (.list vs) → Eval env (.listReverse e) (.list vs.reverse)


/-- Evaluating a well-typed expression produces a value of its inferred type.

`ECons` needs no premise relating the new element to the rest of the list: `Expression.infer`
already requires the tail to be a list of the element type read off the head, so the values
`ECons` builds are homogeneous whenever the expression it evaluates is well typed.

`EVarRef` is the one rule that reads a value it did not build, so it is the one rule that needs
`henv`: the type inferred for a variable is the context's, and only `Env.HasType` ties that to the
value the environment hands back.  It is also the rule that resolves a global, and the two halves of
it line up because `Env.lookup` searches the bindings before the globals exactly as the context
`ctx ++ Globals.types env.globals` is searched left to right.

`EApp` is where the context stops being fixed, which is why the induction generalizes it: the
closure's body was checked against a context of its own, recovered from the closure's type, and has
nothing to do with the one the call was made in.  The argument-evaluation premise contributes
nothing here — `ArgsHaveType` already says what the argument values are, so the types the arguments
were *inferred* to have are only needed to line that up with the closure's parameters. -/
public theorem Eval.hasType {env : Env} {ctx : Context} {e : Expression} {v : Value} {t : Ty}
    (h : Eval env e v) (henv : Env.HasType env ctx)
    (ht : e.infer (ctx ++ Globals.types env.globals) = some t) : v.HasType t := by
  induction h generalizing ctx t with
  | @EVarRef v env x hx =>
      obtain ⟨hgs, hdom, hval⟩ := henv
      rw [Expression.infer_varRef, Context.lookup_append] at ht
      cases hb : env.bindings.lookup x with
      | some v' =>
          obtain ⟨t', hct⟩ := Option.isSome_iff_exists.mp (hdom x (by simp [hb]))
          obtain ⟨v'', hv'', hty⟩ := hval x t' hct
          rw [Env.lookup_of_bindings hb] at hx
          rw [hct] at ht
          grind
      | none =>
          have hcn : ctx.lookup x = none := by
            cases hc : ctx.lookup x with
            | none => rfl
            | some t' => obtain ⟨v', hv', -⟩ := hval x t' hc; simp [hv'] at hb
          rw [Env.lookup_of_globals hb] at hx
          rw [hcn, Globals.lookup_types] at ht
          obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp ht
          rw [hd, Option.map_some] at hx
          obtain rfl : v = Globals.value env.globals d := (Option.some.inj hx).symm
          refine Value.hasType_closure_iff.mpr ⟨[], d.resultType, ?_, ?_, ?_⟩
          · simpa [Globals.value] using Globals.hasType_env hgs
          · simpa [Globals.value, Globals.env] using
              Decl.wellTyped_iff_infer_eq_some.mp (hgs x d hd)
          · simp [Decl.ty]
  | ECons e₁ e₂ h₁ h₂ ih₁ ih₂ =>
      obtain ⟨t', ht₁, ht₂, rfl⟩ := Expression.infer_lcons_eq_some.mp ht
      have hv := ih₁ henv ht₁
      cases ih₂ henv ht₂ with
      | list hall => exact .list (by grind)
  | ELam ps body =>
      obtain ⟨r, hbody, rfl⟩ := Expression.infer_lam_eq_some.mp ht
      exact Value.hasType_closure_iff.mpr ⟨ctx, r, henv, by simpa using hbody, rfl⟩
  | EApp f args hf _ _ hat hbody ihf _ ihbody =>
      obtain ⟨ps', hfty, _⟩ := Expression.infer_app_eq_some.mp ht
      obtain ⟨cctx, r, hcenv, hbodyty, heq⟩ := Value.hasType_closure_iff.mp (ihf henv hfty)
      injection heq with _ hr
      refine ihbody (Env.hasType_extend hat hcenv) ?_
      simp only [Env.globals_extend]
      exact hr ▸ hbodyty
  | _ => grind [Value.HasType]

/-- The environment a call to `d` evaluates its body in: each parameter name bound to its
argument, over the globals and nothing else.

`Env.lookup` reads the first binding of a name, so a parameter repeated in `d.parameters` takes
the argument of its leftmost occurrence, and a parameter named like a global shadows it. -/
public def Decl.callEnv (d : Decl) (gs : Globals) (args : List Value) : Env :=
  (Globals.env gs).extend d.parameters args

/-- `Apply d gs args v`: calling `d` with `args` among the globals `gs` returns `v`.

A call binds the parameters to the arguments positionally and evaluates the body under those
bindings over `gs`, so a body mentioning a name that is neither a parameter nor a global has no
value.

The `ArgsHaveType` premise is what makes a call with the wrong arguments stuck rather than junk:
arguments of the wrong type, or the wrong number of them, produce no value at all.  It is also
all `Apply.hasType` needs to read `d.parameters` as the context the body was checked in. -/
public inductive Decl.Apply (d : Decl) (gs : Globals) : List Value → Value → Prop where
| EApply (args : List Value) :
    ArgsHaveType d.parameters args → Eval (d.callEnv gs args) d.body v → Apply d gs args v

/-- Binding well-typed arguments to a declaration's parameters over its globals gives an environment
the parameter list describes.

`Decl.parameters` is a `Context`, so this is what lets a call use it as one: the types the
body was written against and the types the arguments arrive with are the same list. -/
public theorem Env.hasType_callEnv {d : Decl} {gs : Globals} {args : List Value}
    (hgs : Globals.WellTyped gs) (h : ArgsHaveType d.parameters args) :
    Env.HasType (d.callEnv gs args) d.parameters := by
  simpa [Decl.callEnv] using Env.hasType_extend h (Globals.hasType_env hgs)

/-- Calling a well-typed declaration among well-typed globals returns a value of its declared result
type.

Unlike `Eval.hasType` this needs no hypothesis about the local environment: `Apply` already requires
the arguments to match the parameters, and `Env.hasType_callEnv` turns that into the agreement
between environment and context that `Eval.hasType` asks for.  What is left is a property of the
declaration and the globals alone — nothing about this particular call. -/
public theorem Decl.Apply.hasType {d : Decl} {gs : Globals} {args : List Value} {v : Value}
    (h : d.Apply gs args v) (hgs : Globals.WellTyped gs) (hd : d.WellTyped gs) :
    v.HasType d.resultType := by
  cases h with
  | EApply _ hargs hbody =>
      exact hbody.hasType (Env.hasType_callEnv hgs hargs) (by simpa [Decl.callEnv] using hd)

/-- Every declaration in a well-typed globals table is well typed, so a call to any of them returns
a value of the type it declares. -/
public theorem Globals.apply_hasType {gs : Globals} {x : String} {d : Decl} {args : List Value}
    {v : Value} (hgs : Globals.WellTyped gs) (hx : gs.lookup x = some d)
    (h : d.Apply gs args v) : v.HasType d.resultType :=
  h.hasType hgs (hgs x d hx)

/-- `p.Apply x args v`: calling the declaration `p` gives the name `x` with `args` returns `v`.

The body runs among `p`'s own globals, so it may call anything else `p` declares — itself
included.  A name `p` does not declare has no call at all, which is the only way this differs from
`Decl.Apply` on `p.globals`. -/
public inductive Program.Apply (p : Program) (x : String) : List Value → Value → Prop where
| call (d : Decl) : p.lookup x = some d → d.Apply p.globals args v → Apply p x args v

/-- Calling a name in a well-typed program returns a value of the type the declaration under that
name declares.

This is the top of the stack: `Program.WellTyped` is a property of the program alone, checked once
by `Program.check`, and it covers every call to every name in it. -/
public theorem Program.Apply.hasType {p : Program} {x : String} {d : Decl} {args : List Value}
    {v : Value} (h : p.Apply x args v) (hp : p.WellTyped) (hx : p.lookup x = some d) :
    v.HasType d.resultType := by
  cases h with
  | call d' hx' hbody =>
      obtain rfl : d' = d := by grind
      exact Globals.apply_hasType hp hx' hbody

section Tests

/-- Add `x` to one less than `y`. -/
lgtm private def addPred as "add-pred" (x : int) (y : int) : int :=
  x + (y - 1)

-- This is a simple proof demonstrating how proofs work through the
-- relational evaluator
private theorem addPred.trivial_positive
  (x y res : Value)
  (hXPos : ∀ xv, .int xv = x → xv >= 1)
  (hYPos : ∀ yv, .int yv = y → yv >= 1)
  (hRes : Decl.Apply addPred [] [ x, y ] res) :
  ∃ resv, res = .int resv ∧ resv > 0 := by
  obtain ⟨-, -, hbody⟩ := hRes
  cases hbody with
  | EPlus _ _ h₁ h₂ =>
    cases h₁ with
    | EVarRef _ hlx =>
      cases h₂ with
      | EMinus _ _ h₃ h₄ =>
        cases h₃ with
        | EVarRef _ hly =>
          cases h₄ with
          | EIntLit _ =>
            simp [addPred, Decl.callEnv, Env.extend, Globals.env, Env.lookup, List.lookup]
              at hlx hly
            grind

-- A call evaluates its body under the arguments, read back out by `EVarRef`.
example : Decl.Apply addPred [] [.int 2, .int 5] (.int 6) :=
  .EApply _ (.cons "x" (.int 2) (.cons "y" (.int 5) .nil))
    (.EPlus (n₁ := 2) (n₂ := 5 - 1) _ _ (.EVarRef "x" rfl)
      (.EMinus _ _ (.EVarRef "y" rfl) (.EIntLit 1)))

-- Whatever a call returns has the declared result type, and it is `addPred` being well typed that
-- says so, not anything about these particular arguments.
example (v : Value) (h : Decl.Apply addPred [] [.int 2, .int 5] v) : v.HasType .int :=
  h.hasType Globals.wellTyped_nil (by simp [addPred, List.lookup])

-- A call with the wrong number of arguments is stuck, whether or not the body would have needed
-- the missing one.
example (v : Value) : ¬ Decl.Apply addPred [] [.int 2] v := by
  rintro ⟨-, hargs, -⟩
  cases hargs with
  | cons _ _ hrest => cases hrest

example (v : Value) : ¬ Decl.Apply addPred [] [.int 2, .int 5, .int 8] v := by
  rintro ⟨-, hargs, -⟩
  cases hargs with
  | cons _ _ hrest => cases hrest with | cons _ _ hrest => cases hrest

/-- Put `x` on the front of `xs`. -/
lgtm private def cons (x : int) (xs : list int) : list int :=
  x :: xs

/-- A one-element list is homogeneous for the reason its only element is. -/
private theorem hasType_singleton {v : Value} {t : Ty} (h : v.HasType t) :
    Value.HasType (.list [v]) (.list t) := .list (by simpa using h)

example : Decl.Apply cons [] [.int 1, .list [.int 2]] (.list [.int 1, .int 2]) :=
  .EApply _ (.cons "x" (.int 1) (.cons "xs" (hasType_singleton (.int 2)) .nil))
    (.ECons _ _ (.EVarRef "x" rfl) (.EVarRef "xs" rfl))

-- An argument of the wrong type is now rejected at the call itself, rather than getting the body
-- stuck once it is looked up.
example (v : Value) : ¬ Decl.Apply cons [] [.int 1, .int 2] v := by
  rintro ⟨-, hargs, -⟩
  cases hargs with
  | cons _ _ hrest => cases hrest with | cons _ hv _ => cases hv

/-- Reverse `xs` with `x` on the front. -/
lgtm private def revCons as "rev-cons" (x : int) (xs : list int) : list int :=
  reverse (x :: xs)

/-- A list of `int`s is homogeneous at `.list .int`, whatever its length. -/
private theorem hasType_intList {is : List Int} :
    Value.HasType (.list (is.map .int)) (.list .int) :=
  .list (by simpa using fun i (_ : i ∈ is) => Value.HasType.int i)

-- `EListReverse` runs on the list `ECons` has just built, so the element pushed on the front comes
-- back last.
example : Decl.Apply revCons [] [.int 1, .list [.int 2, .int 3]] (.list [.int 3, .int 2, .int 1]) :=
  .EApply _ (.cons "x" (.int 1) (.cons "xs" (hasType_intList (is := [2, 3])) .nil))
    (.EListReverse (vs := [.int 1, .int 2, .int 3]) _
      (.ECons _ _ (.EVarRef "x" rfl) (.EVarRef "xs" rfl)))

-- Reversing preserves the element type, so soundness gives the declared result type back with no
-- reasoning about this particular list.
example (v : Value) (h : Decl.Apply revCons [] [.int 1, .list [.int 2, .int 3]] v) :
    v.HasType (.list .int) :=
  h.hasType Globals.wellTyped_nil (by simp [revCons, List.lookup])

-- Only a list can be reversed, so a body reversing one of the `int` parameters does not check.
example : ¬ ({ revCons with body := [lgtm| reverse x] } : Decl).WellTyped [] := by
  simp [revCons, List.lookup]

/-- Reverse `xs` twice, which gives `xs` back. -/
lgtm private def reverseTwice as "reverse-twice" (xs : list int) : list int :=
  reverse (reverse xs)

/-- Reversing twice is the identity.

Inverting the two `EListReverse` steps down to the `EVarRef` that read `xs` leaves exactly
`List.reverse_reverse`, so this is a property of the program proved from the evaluator rather than
from any one input. -/
private theorem reverseTwice.eq_self {vs : List Value} {res : Value}
    (h : Decl.Apply reverseTwice [] [.list vs] res) : res = .list vs := by
  obtain ⟨-, -, hbody⟩ := h
  cases hbody with
  | EListReverse _ h₁ =>
    cases h₁ with
    | EListReverse _ h₂ =>
      cases h₂ with
      | EVarRef _ hlx =>
        simp [reverseTwice, Decl.callEnv, Env.extend, Globals.env, Env.lookup] at hlx
        grind

/-- The body of the inner lambda of `adderExpr`, `x + n`, which needs an `n` from outside itself. -/
private def adderInner : Expression := [lgtm| x + n]

/-- A function that builds a function.  Spliced together from `adderInner` rather than written out
so that the two are the same term, which the closures below are stated in terms of. -/
private def adderExpr : Expression := [lgtm| fun (n : int) => fun (x : int) => ~(adderInner)]

/-- The empty environment describes the empty context, which is all these examples need to say
about their environment. -/
private theorem hasType_nil : Env.HasType ∅ [] :=
  ⟨by simpa using Globals.wellTyped_nil, by simp, by simp⟩

-- Nothing in a lambda's body runs until it is applied; evaluating one only captures the
-- environment it was reached in.
example : Eval ∅ adderExpr (.closure ∅ [("n", .int)] [lgtm| fun (x : int) => ~(adderInner)]) :=
  .ELam _ _

/-- Applying the outer lambda runs its body, which is itself a lambda, so what comes back is a
closure that has captured `n`. -/
private theorem eval_adder10 :
    Eval ∅ [lgtm| ~(adderExpr)(10)] (.closure ⟨[("n", .int 10)], []⟩ [("x", .int)] adderInner) :=
  .EApp (vs := [.int 10]) _ _ (.ELam _ _) rfl
    (by rintro ⟨e, v⟩ hp; simp at hp; obtain ⟨rfl, rfl⟩ := hp; exact .EIntLit 10)
    (.cons "n" (.int 10) .nil) (.ELam _ _)

-- Applying that closure is what finally runs `x + n`, and it runs in the environment the closure
-- captured rather than the one the call was made from: `n` is in scope even though the caller's
-- environment is empty.
example : Eval ∅ [lgtm| ~(adderExpr)(10)(1)] (.int 11) :=
  .EApp (vs := [.int 1]) _ _ eval_adder10 rfl
    (by rintro ⟨e, v⟩ hp; simp at hp; obtain ⟨rfl, rfl⟩ := hp; exact .EIntLit 1)
    (.cons "x" (.int 1) .nil)
    (.EPlus (n₁ := 1) (n₂ := 10) _ _ (.EVarRef "x" rfl) (.EVarRef "n" rfl))

-- Soundness covers the new forms: a value of function type comes back, and which context the
-- closure captured is the theorem's business rather than the caller's.
example (v : Value) (h : Eval ∅ [lgtm| ~(adderExpr)(10)] v) : v.HasType (.fn [.int] .int) :=
  h.hasType hasType_nil (by simp [adderExpr, adderInner, List.lookup])

-- A call with the wrong number of arguments is stuck, just as it is for a declaration: the
-- parameters `ArgsHaveType` walks are the closure's own, so the lengths cannot disagree.
example (v : Value) : ¬ Eval ∅ [lgtm| ~(adderExpr)(1, 2)] v := by
  intro h
  cases h with
  | EApp f args hf hlen hargs hat hbody =>
      simp only [adderExpr] at hf
      cases hf
      cases hat with
      | cons _ _ hrest => cases hrest; simp at hlen

-- An argument of the wrong type is stuck too, so a closure cannot be entered with arguments its
-- parameters do not describe.
example (v : Value) : ¬ Eval ∅ [lgtm| ~(adderExpr)("a")] v := by
  intro h
  cases h with
  | EApp f args hf hlen hargs hat hbody =>
      simp only [adderExpr] at hf
      cases hf
      cases hat with
      | cons _ hv hrest =>
          cases hrest
          cases hargs _ (List.mem_cons_self ..)
          cases hv

/-- Build a function that adds `n` to its argument. -/
lgtm private def adder (n : int) : (int) -> int :=
  fun (m : int) => n + m

-- A declaration can return a function, and `Decl.Apply.hasType` covers that result type like any
-- other: what comes back is a closure, and the theorem says it is one of the declared type.
example (v : Value) (h : Decl.Apply adder [] [.int 3] v) : v.HasType (.fn [.int] .int) :=
  h.hasType Globals.wellTyped_nil (by simp [adder, List.lookup])

/-! ## Globals

Everything above ran with an empty table, so every name a body mentioned was one of its own
parameters.  These declare a table and call across it. -/

/-- Twice `n`. -/
lgtm private def double (n : int) : int :=
  n + n

/-- Four times `n`, which is `double` calling `double`. -/
lgtm private def quad (n : int) : int :=
  double(double(n))

/-- One more than twice `n`. -/
lgtm private def doublePlus as "double-plus" (n : int) : int :=
  double(n) + 1

/-- The answer.  A declaration of no parameters is how a global *variable* is written: its name has
type `() -> int`, so reading it is the call `answer()`. -/
lgtm private def answer : int :=
  42

/-- One more than the answer, which is where the nullary global gets read. -/
lgtm private def answerPlus as "answer-plus" : int :=
  answer() + 1

private def arith : Globals := Globals.ofDecls [double, quad, doublePlus, answer, answerPlus]

-- A body may mention a global, and `Decl.check` finds it at the type its declaration gives.
#guard quad.check arith
#guard answerPlus.check arith
#guard Globals.check arith

-- Without the table the same name is free, and the body does not check.  This is all `Globals` adds
-- to the checker: `double` has a type in `quad`'s body only because `arith` says so.
#guard !quad.check []
#guard !answerPlus.check []

-- The arity is the declaration's, so a global is as picky about how many arguments it gets as any
-- other function, and a nullary global has to be called rather than just named.
#guard !({ quad with body := [lgtm| double(1, 2)] } : Decl).check arith
#guard !({ answerPlus with body := [lgtm| answer + 1] } : Decl).check arith

-- A parameter shadows a global of the same name, in the checker and in `Env.lookup` alike.
#guard ({ quad with parameters := [("double", .int)], body := [lgtm| double] } : Decl).check arith
#guard !({ quad with parameters := [("double", .int)], body := [lgtm| double(1)] } : Decl).check
  arith

-- A name that is neither a parameter nor a global is still free.
#guard !({ double with body := [lgtm| missing(n)] } : Decl).check arith

/-- Every declaration in `arith` checks, which is what a call to any of them needs. -/
private theorem arith.wellTyped : Globals.WellTyped arith := by
  refine Globals.wellTyped_of_forall fun p hp => ?_
  simp only [arith, Globals.ofDecls, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    simp [double, quad, doublePlus, answer, answerPlus, arith, Globals.ofDecls,
      Decl.ty, List.lookup]

/-- A call across the table: `double` is not bound in `doublePlus`'s call environment, so
`Env.lookup` falls through to the globals and builds its closure there.

The body then runs in *that* closure's environment — `double`'s own parameter over the same globals
— and not in the one the call was made from. -/
private theorem eval_doublePlus : Decl.Apply doublePlus arith [.int 3] (.int 7) :=
  .EApply _ (.cons "n" (.int 3) .nil)
    (.EPlus (n₁ := 6) (n₂ := 1) _ _
      (.EApp (vs := [.int 3]) _ _ (.EVarRef "double" rfl) rfl
        (by rintro ⟨e, v⟩ hp; simp at hp; obtain ⟨rfl, rfl⟩ := hp; exact .EVarRef "n" rfl)
        (.cons "n" (.int 3) .nil)
        (.EPlus (n₁ := 3) (n₂ := 3) _ _ (.EVarRef "n" rfl) (.EVarRef "n" rfl)))
      (.EIntLit 1))

-- Soundness covers a call that goes through the table, and the reason is that every declaration in
-- `arith` checks — nothing about this particular call.
example (v : Value) (h : Decl.Apply doublePlus arith [.int 3] v) : v.HasType .int :=
  h.hasType arith.wellTyped (arith.wellTyped "double-plus" doublePlus rfl)

-- `Globals.apply_hasType` is that statement read off the table, for whichever entry a name resolves
-- to, so the caller needs no `Decl.WellTyped` of its own.
example (v : Value) (h : Decl.Apply answerPlus arith [] v) : v.HasType .int :=
  Globals.apply_hasType (x := "answer-plus") arith.wellTyped rfl h

/-- Recursion is what a table of declarations buys over a table of values: `countdown` is checked in
a context that already holds `countdown`, so it may call itself. -/
lgtm private def countdown (n : int) : int :=
  countdown(n - 1)

#guard Globals.check (Globals.ofDecls [countdown])
#guard !countdown.check []

/-- Mutual recursion needs nothing further: both are in the context both are checked against. -/
lgtm private def ping (n : int) : int :=
  pong(n - 1)

lgtm private def pong (n : int) : int :=
  ping(n - 1)

#guard Globals.check (Globals.ofDecls [ping, pong])

-- Neither checks alone, and neither checks with only itself in scope: it is the table that ties
-- them together.
#guard !ping.check []
#guard !ping.check (Globals.ofDecls [ping])
#guard !Globals.check (Globals.ofDecls [ping])

/-! ## Programs

The same declarations again, read as a source file rather than as a table: `arith` is what
`arithProgram` presents to its own bodies. -/

private def arithProgram : Program := ⟨[double, quad, doublePlus, answer, answerPlus]⟩

example : arithProgram.globals = arith := rfl

#guard arithProgram.check

-- A program resolves the names its declarations declare, so `as` is what shows up here and the Lean
-- name does not.
example : arithProgram.lookup "double-plus" = some doublePlus := rfl
example : arithProgram.lookup "doublePlus" = none := rfl
example : arithProgram.lookup "missing" = none := rfl

-- No two of them share a name, so none is shadowed and every one can be called.
example : arithProgram.NamesUnique := by decide
example : ¬ ({ decls := [double, double] } : Program).NamesUnique := by decide

-- Which is what `lookup_self` is for: being one of the program's declarations is enough.
example : arithProgram.lookup quad.name = some quad :=
  arithProgram.lookup_self (by decide) (by simp [arithProgram])

-- A duplicate name is not unsound, just dead: the second declaration is checked and unreachable.
#guard ({ decls := [double, { double with resultType := .int }] } : Program).check
example : ({ decls := [answer, { answer with resultType := .string }] } : Program).lookup "answer"
    = some answer := rfl

/-- `arithProgram` checks, which is a property of the program alone. -/
private theorem arithProgram.wellTyped : arithProgram.WellTyped := arith.wellTyped

-- Running a program is calling one of its names, and the body runs among the program's own
-- declarations.
example : arithProgram.Apply "double-plus" [.int 3] (.int 7) :=
  .call _ rfl eval_doublePlus

-- Soundness at the top: one hypothesis about the whole program covers every call to every name in
-- it, whatever the arguments.
example (v : Value) (h : arithProgram.Apply "double-plus" [.int 3] v) : v.HasType .int :=
  h.hasType arithProgram.wellTyped rfl

example (v : Value) (args : List Value) (h : arithProgram.Apply "answer-plus" args v) :
    v.HasType .int :=
  h.hasType arithProgram.wellTyped rfl

-- A name the program does not declare has no call at all.
example (v : Value) : ¬ arithProgram.Apply "missing" [.int 3] v := by
  rintro ⟨d, hd, -⟩
  rw [show arithProgram.lookup "missing" = none from rfl] at hd
  simp at hd

end Tests
