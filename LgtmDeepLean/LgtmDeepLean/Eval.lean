module

public import LgtmDeepLean.IR
public import LgtmDeepLean.TypeCheck

public inductive Value where
| int : Int → Value
| string : String → Value
| list : List Value → Value
/-- A function together with the environment it was written in.

The parameters are annotated the way `lam` annotates them, so a closure carries everything needed
to say what type it has.  Spelled `List (String × Value)` rather than `Env` only because `Env` is
this type's own abbreviation and cannot be named yet. -/
| closure : List (String × Value) → List (String × Ty) → Expression → Value

public abbrev Env := List (String × Value)

/-- The `Ty` a value's representation agrees with.

A list value is homogeneous: every element has the list's single element type.

A closure has a function type when its body checks against the result type under its parameters and
*some* context its captured environment agrees with.  That agreement is `Env.HasType`, but it cannot
be named here — `Env.HasType` is a definition, and it is defined in terms of `Value.HasType` — and it
cannot even be written out as it stands, because the kernel refuses a recursive occurrence under an
`∃`.  So the two halves of it are separated: the captured environment binds every name the context
promises, and every value it binds has the type promised for it.  `Value.hasType_closure_iff` puts
them back together and is the form to use. -/
public inductive Value.HasType : Value → Ty → Prop where
| int (i : Int) : HasType (.int i) .int
| string (s : String) : HasType (.string s) .string
| list {vs : List Value} {t : Ty} : (∀ v ∈ vs, HasType v t) → HasType (.list vs) (.list t)
| closure {cenv : Env} {ps : Context} {body : Expression} {cctx : Context} {r : Ty} :
    (∀ x, (cctx.lookup x).isSome → (cenv.lookup x).isSome) →
    (∀ x t v, cctx.lookup x = some t → cenv.lookup x = some v → HasType v t) →
    body.infer (ps ++ cctx) = some r →
    HasType (.closure cenv ps body) (.fn (ps.map Prod.snd) r)

/-- `env` supplies every binding `ctx` promises, at the type `ctx` gives it.

This is the environment-level counterpart of `Value.HasType`: it is what makes a `varRef` safe to
evaluate, and it is the only thing `Eval.hasType` needs to know about an environment. -/
public def Env.HasType (env : Env) (ctx : Context) : Prop :=
  ∀ x t, ctx.lookup x = some t → ∃ v, env.lookup x = some v ∧ v.HasType t

/-- What it takes for a closure to have a type, in terms of `Env.HasType`.

The context is existential: a closure's type says nothing about which names it captured, only that
whatever it captured was enough to type its body. -/
@[simp] public theorem Value.hasType_closure_iff {cenv : Env} {ps : Context} {body : Expression}
    {t : Ty} :
    Value.HasType (.closure cenv ps body) t ↔
      ∃ cctx r, Env.HasType cenv cctx ∧ body.infer (ps ++ cctx) = some r
        ∧ t = .fn (ps.map Prod.snd) r := by
  constructor
  · intro h
    cases h with
    | closure hbinds htypes hbody =>
        refine ⟨_, _, fun x t hx => ?_, hbody, rfl⟩
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hbinds x (by simp [hx]))
        exact ⟨v, hv, htypes x t v hx hv⟩
  · rintro ⟨cctx, r, hcenv, hbody, rfl⟩
    refine .closure (fun x hx => ?_) (fun x t v hx hv => ?_) hbody
    · obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hx
      obtain ⟨v, hv, -⟩ := hcenv x t ht
      simp [hv]
    · obtain ⟨v', hv', hty⟩ := hcenv x t hx
      grind

/-- `env` with each name in `ps` bound to the value in `vs` at the same position, in front of what
`env` had, so the new bindings shadow it.

`List.zip` stops at the shorter list, so this only describes a call once the two are known to be the
same length; `ArgsHaveType` is what supplies that. -/
public def Env.extend (env : Env) (ps : Context) (vs : List Value) : Env :=
  (ps.map Prod.fst).zip vs ++ env

/-- `ArgsHaveType ps args`: `args` are values a function with parameters `ps` can be called with,
one argument per parameter and each of the type its parameter declares.

Walking the two lists together also pins the arity down: a call passing too few or too many
arguments has no such proof. -/
public inductive ArgsHaveType : Context → List Value → Prop where
| nil : ArgsHaveType [] []
| cons (x : String) : v.HasType t → ArgsHaveType ps args → ArgsHaveType ((x, t) :: ps) (v :: args)

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
  | cons _ hv _ ih =>
      intro x t hx
      simp only [Env.extend, List.map_cons, List.zip_cons_cons, List.cons_append,
        List.lookup_cons] at hx ⊢
      split at hx
      · exact ⟨_, rfl, by grind⟩
      · exact ih x t hx

/-- Binding well-typed arguments to their parameters gives an environment the parameter list
describes.

`Decl.parameters` is a `Context`, so this is what lets a call use it as one: the types the
body was written against and the types the arguments arrive with are the same list. -/
public theorem Env.hasType_zip {ps : Context} {args : List Value}
    (h : ArgsHaveType ps args) : Env.HasType ((ps.map Prod.fst).zip args) ps := by
  have hnil : Env.HasType [] [] := by intro x t hx; simp at hx
  simpa [Env.extend] using Env.hasType_extend h hnil

/-- `env` is an index rather than a parameter because `EApp` evaluates a body in the environment its
closure captured, not in the one the call was made from. -/
public inductive Eval : Env → Expression → Value → Prop where
| EVarRef (x : String) : env.lookup x = some v → Eval env (.varRef x) v
| EIntLit (i : Int) : Eval env (.intLit i) (.int i)
| EPlus (e₁ : Expression) (e₂ : Expression) : Eval env e₁ (.int n₁) → Eval env e₂ (.int n₂) → Eval env (.plus e₁ e₂) (.int (n₁ + n₂))
| EMinus (e₁ : Expression) (e₂ : Expression) : Eval env e₁ (.int n₁) → Eval env e₂ (.int n₂) → Eval env (.minus e₁ e₂) (.int (n₁ - n₂))
| EStringLit (s : String) : Eval env (.stringLit s) (.string s)
| ENil (ty : Ty) : Eval env (.lnil ty) (.list [])
| ECons (e₁ : Expression) (e₂ : Expression) : Eval env e₁ v → Eval env e₂ (.list vs) → Eval env (.lcons e₁ e₂) (.list (v :: vs))
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

/-- Evaluating a well-typed expression produces a value of its inferred type.

`ECons` needs no premise relating the new element to the rest of the list: `Expression.infer`
already requires the tail to be a list of the element type read off the head, so the values
`ECons` builds are homogeneous whenever the expression it evaluates is well typed.

`EVarRef` is the one rule that reads a value it did not build, so it is the one rule that needs
`henv`: the type inferred for a variable is the context's, and only `Env.HasType` ties that to the
value the environment hands back.

`EApp` is where the context stops being fixed, which is why the induction generalizes it: the
closure's body was checked against a context of its own, recovered from the closure's type, and has
nothing to do with the one the call was made in.  The argument-evaluation premise contributes
nothing here — `ArgsHaveType` already says what the argument values are, so the types the arguments
were *inferred* to have are only needed to line that up with the closure's parameters. -/
public theorem Eval.hasType {env : Env} {ctx : Context} {e : Expression} {v : Value} {t : Ty}
    (h : Eval env e v) (henv : Env.HasType env ctx) (ht : e.infer ctx = some t) : v.HasType t := by
  induction h generalizing ctx t with
  | EVarRef x hx =>
      obtain ⟨v', hv', hty⟩ := henv x t (by simpa using ht)
      grind
  | ECons e₁ e₂ h₁ h₂ ih₁ ih₂ =>
      obtain ⟨t', ht₁, ht₂, rfl⟩ := Expression.infer_lcons_eq_some.mp ht
      have hv := ih₁ henv ht₁
      cases ih₂ henv ht₂ with
      | list hall => exact .list (by grind)
  | ELam ps body =>
      obtain ⟨r, hbody, rfl⟩ := Expression.infer_lam_eq_some.mp ht
      exact Value.hasType_closure_iff.mpr ⟨ctx, r, henv, hbody, rfl⟩
  | EApp f args hf _ _ hat hbody ihf _ ihbody =>
      obtain ⟨ps', hfty, _⟩ := Expression.infer_app_eq_some.mp ht
      obtain ⟨cctx, r, hcenv, hbodyty, heq⟩ := Value.hasType_closure_iff.mp (ihf henv hfty)
      injection heq with _ hr
      exact ihbody (Env.hasType_extend hat hcenv) (hr ▸ hbodyty)
  | _ => grind [Value.HasType]

/-- The environment a call to `d` evaluates its body in: each parameter name bound to its
argument, and nothing else.

`List.lookup` reads the first binding of a name, so a parameter repeated in `d.parameters` takes
the argument of its leftmost occurrence. -/
public def Decl.callEnv (d : Decl) (args : List Value) : Env :=
  (d.parameters.map Prod.fst).zip args

/-- `Apply d args v`: calling `d` with `args` returns `v`.

A call binds the parameters to the arguments positionally and evaluates the body under those
bindings and nothing else, so a body mentioning any other name has no value.

The `ArgsHaveType` premise is what makes a call with the wrong arguments stuck rather than junk:
arguments of the wrong type, or the wrong number of them, produce no value at all.  It is also
all `Apply.hasType` needs to read `d.parameters` as the context the body was checked in. -/
public inductive Decl.Apply (d : Decl) : List Value → Value → Prop where
| EApply (args : List Value) :
    ArgsHaveType d.parameters args → Eval (d.callEnv args) d.body v → Apply d args v

/-- Calling a well-typed declaration returns a value of its declared result type.

Unlike `Eval.hasType` this needs no hypothesis about the environment: `Apply` already requires the
arguments to match the parameters, and `Env.hasType_zip` turns that into the agreement between
environment and context that `Eval.hasType` asks for.  What is left, `Decl.WellTyped`, is a
property of the declaration alone — nothing about this particular call. -/
public theorem Decl.Apply.hasType {d : Decl} {args : List Value} {v : Value}
    (h : d.Apply args v) (hd : d.WellTyped) : v.HasType d.resultType := by
  cases h with
  | EApply _ hargs hbody => exact hbody.hasType (Env.hasType_zip hargs) (by grind)

section Tests

/-- `fun (x : int) (y : int) => x + (y - 1)` -/
private def addPred : Decl where
  docstring := "Add `x` to one less than `y`."
  name := "add-pred"
  parameters := [("x", .int), ("y", .int)]
  body := .plus (.varRef "x") (.minus (.varRef "y") (.intLit 1))
  resultType := .int

-- This is a simple proof demonstrating how proofs work through the
-- relational evaluator
private theorem addPred.trivial_positive
  (x y res : Value)
  (hXPos : ∀ xv, .int xv = x → xv >= 1)
  (hYPos : ∀ yv, .int yv = y → yv >= 1)
  (hRes : Decl.Apply addPred [ x, y ] res) :
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
            simp [addPred, Decl.callEnv, List.lookup] at hlx hly
            grind

-- A call evaluates its body under the arguments, read back out by `EVarRef`.
example : Decl.Apply addPred [.int 2, .int 5] (.int 6) :=
  .EApply _ (.cons "x" (.int 2) (.cons "y" (.int 5) .nil))
    (.EPlus (n₁ := 2) (n₂ := 5 - 1) _ _ (.EVarRef "x" rfl)
      (.EMinus _ _ (.EVarRef "y" rfl) (.EIntLit 1)))

-- Whatever a call returns has the declared result type, and it is `addPred` being well typed that
-- says so, not anything about these particular arguments.
example (v : Value) (h : Decl.Apply addPred [.int 2, .int 5] v) : v.HasType .int :=
  h.hasType (by simp [addPred, List.lookup])

-- A call with the wrong number of arguments is stuck, whether or not the body would have needed
-- the missing one.
example (v : Value) : ¬ Decl.Apply addPred [.int 2] v := by
  rintro ⟨-, hargs, -⟩
  cases hargs with
  | cons _ _ hrest => cases hrest

example (v : Value) : ¬ Decl.Apply addPred [.int 2, .int 5, .int 8] v := by
  rintro ⟨-, hargs, -⟩
  cases hargs with
  | cons _ _ hrest => cases hrest with | cons _ _ hrest => cases hrest

/-- `fun (x : int) (xs : list int) => x :: xs` -/
private def cons : Decl where
  docstring := "Put `x` on the front of `xs`."
  name := "cons"
  parameters := [("x", .int), ("xs", .list .int)]
  body := .lcons (.varRef "x") (.varRef "xs")
  resultType := .list .int

/-- A one-element list is homogeneous for the reason its only element is. -/
private theorem hasType_singleton {v : Value} {t : Ty} (h : v.HasType t) :
    Value.HasType (.list [v]) (.list t) := .list (by simpa using h)

example : Decl.Apply cons [.int 1, .list [.int 2]] (.list [.int 1, .int 2]) :=
  .EApply _ (.cons "x" (.int 1) (.cons "xs" (hasType_singleton (.int 2)) .nil))
    (.ECons _ _ (.EVarRef "x" rfl) (.EVarRef "xs" rfl))

-- An argument of the wrong type is now rejected at the call itself, rather than getting the body
-- stuck once it is looked up.
example (v : Value) : ¬ Decl.Apply cons [.int 1, .int 2] v := by
  rintro ⟨-, hargs, -⟩
  cases hargs with
  | cons _ _ hrest => cases hrest with | cons _ hv _ => cases hv

/-- The body of the inner lambda of `adderExpr`, `x + n`, which needs an `n` from outside itself. -/
private def adderInner : Expression := .plus (.varRef "x") (.varRef "n")

/-- `fun (n : int) => fun (x : int) => x + n`: a function that builds a function. -/
private def adderExpr : Expression := .lam [("n", .int)] (.lam [("x", .int)] adderInner)

/-- The empty environment describes the empty context, which is all these examples need to say
about their environment. -/
private theorem hasType_nil : Env.HasType [] [] := by intro x t hx; simp at hx

-- Nothing in a lambda's body runs until it is applied; evaluating one only captures the
-- environment it was reached in.
example : Eval [] adderExpr (.closure [] [("n", .int)] (.lam [("x", .int)] adderInner)) :=
  .ELam _ _

/-- Applying the outer lambda runs its body, which is itself a lambda, so what comes back is a
closure that has captured `n`. -/
private theorem eval_adder10 :
    Eval [] (.app adderExpr [.intLit 10]) (.closure [("n", .int 10)] [("x", .int)] adderInner) :=
  .EApp (vs := [.int 10]) _ _ (.ELam _ _) rfl
    (by rintro ⟨e, v⟩ hp; simp at hp; obtain ⟨rfl, rfl⟩ := hp; exact .EIntLit 10)
    (.cons "n" (.int 10) .nil) (.ELam _ _)

-- Applying that closure is what finally runs `x + n`, and it runs in the environment the closure
-- captured rather than the one the call was made from: `n` is in scope even though the caller's
-- environment is empty.
example : Eval [] (.app (.app adderExpr [.intLit 10]) [.intLit 1]) (.int 11) :=
  .EApp (vs := [.int 1]) _ _ eval_adder10 rfl
    (by rintro ⟨e, v⟩ hp; simp at hp; obtain ⟨rfl, rfl⟩ := hp; exact .EIntLit 1)
    (.cons "x" (.int 1) .nil)
    (.EPlus (n₁ := 1) (n₂ := 10) _ _ (.EVarRef "x" rfl) (.EVarRef "n" rfl))

-- Soundness covers the new forms: a value of function type comes back, and which context the
-- closure captured is the theorem's business rather than the caller's.
example (v : Value) (h : Eval [] (.app adderExpr [.intLit 10]) v) : v.HasType (.fn [.int] .int) :=
  h.hasType hasType_nil (by simp [adderExpr, adderInner, List.lookup])

-- A call with the wrong number of arguments is stuck, just as it is for a declaration: the
-- parameters `ArgsHaveType` walks are the closure's own, so the lengths cannot disagree.
example (v : Value) : ¬ Eval [] (.app adderExpr [.intLit 1, .intLit 2]) v := by
  intro h
  cases h with
  | EApp f args hf hlen hargs hat hbody =>
      simp only [adderExpr] at hf
      cases hf
      cases hat with
      | cons _ _ hrest => cases hrest; simp at hlen

-- An argument of the wrong type is stuck too, so a closure cannot be entered with arguments its
-- parameters do not describe.
example (v : Value) : ¬ Eval [] (.app adderExpr [.stringLit "a"]) v := by
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

/-- `fun (n : int) => fun (m : int) => n + m` -/
private def adder : Decl where
  docstring := "Build a function that adds `n` to its argument."
  name := "adder"
  parameters := [("n", .int)]
  body := .lam [("m", .int)] (.plus (.varRef "n") (.varRef "m"))
  resultType := .fn [.int] .int

-- A declaration can return a function, and `Decl.Apply.hasType` covers that result type like any
-- other: what comes back is a closure, and the theorem says it is one of the declared type.
example (v : Value) (h : Decl.Apply adder [.int 3] v) : v.HasType (.fn [.int] .int) :=
  h.hasType (by simp [adder, List.lookup])

end Tests
