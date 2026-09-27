module

public import LgtmDeepLean.IR
public import LgtmDeepLean.TypeCheck
public import LgtmDeepLean.Value
meta import LgtmDeepLean.IR
meta import LgtmDeepLean.TypeCheck
meta import LgtmDeepLean.Value
import LgtmDeepLean.Syntax

/-! # Evaluation

The relational semantics of the IR, and its soundness: evaluating a well-typed expression produces
a value of the type inferred for it.  Values, environments, and what it means for either to have a
type live in `Value.lean`. -/

/-- This is a relational evaluator for expressions under a given `Env` (environment).

This is the bridge from the deeply-embedded DSL to logical terms we can reason about
using standard Lean techniques.  The `Expression` is the DSL term while the `Value` is
how it would be evaluated in Lean.  Proofs are over the latter, which can use the full
Lean standard library. -/
public inductive Eval : Env → Expression → Value → Prop where
| ELam (ps : List (String × Ty)) (body : Expression) : Eval env (.lam ps body) (env.closure ps body)
/-- A call evaluates its function and its arguments, then the body in the closure's environment
extended with the parameters. -/
| EApp (f : Expression) (args : List Expression) :
    Eval env f (.closure cbindings cglobals ps body) →
    args.length = vs.length → (∀ p ∈ args.zip vs, Eval env p.1 p.2) →
    ArgsHaveType ps vs →
    Eval (Env.extend ⟨cbindings, cglobals⟩ ps vs) body v →
    Eval env (.app f args) v
/-- Let binds a variable that shadows any existing bindings.

    The bound value is available in the body of the let.  This is a non-recursive let. -/
| ELet (x : String) (e : Expression) (body : Expression) :
    Eval env e v₁ →
    Eval ⟨(x, v₁) :: env.bindings, env.globals⟩ body v →
    Eval env (.let_ x e body) v
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

`ELet` is the other rule that extends the environment, and it is the easy one: the context grows on
the left exactly as the bindings do, so `Env.hasType_cons` — applied to the type the bound expression
was inferred at — is the whole case.

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
          · exact Globals.hasType_env hgs
          · simpa using Decl.wellTyped_iff_infer_eq_some.mp (hgs x d hd)
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
  | ELet x e body _ _ ih₁ ihbody =>
      obtain ⟨t', ht', htbody⟩ := Expression.infer_let_eq_some.mp ht
      exact ihbody (Env.hasType_cons (ih₁ henv ht') henv) htbody
  | _ => grind [Value.HasType]

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
example :
    Eval ∅ adderExpr ((∅ : Env).closure [("n", .int)] [lgtm| fun (x : int) => ~(adderInner)]) :=
  .ELam _ _

/-- Applying the outer lambda runs its body, which is itself a lambda, so what comes back is a
closure that has captured `n`. -/
private theorem eval_adder10 :
    Eval ∅ [lgtm| ~(adderExpr)(10)] (.closure [("n", .int 10)] [] [("x", .int)] adderInner) :=
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

/-! ## Let bindings

A `let_` is the one form that extends the environment without a call, so these are about what the
binding is and what it is not: it is in scope in the body, and it is not in scope in the expression
it binds. -/

-- A `let` binds the value its expression evaluated to, which `EVarRef` then reads out of the
-- bindings like any other name.
example : Eval ∅ [lgtm| let x = 1 + 2 in x + x] (.int 6) :=
  .ELet _ _ _ (.EPlus (n₁ := 1) (n₂ := 2) _ _ (.EIntLit 1) (.EIntLit 2))
    (.EPlus (n₁ := 3) (n₂ := 3) _ _ (.EVarRef "x" rfl) (.EVarRef "x" rfl))

-- Twice, so a later binding sees an earlier one.
example : Eval ∅ [lgtm| let x = 1 in let y = x + 1 in x + y] (.int 3) :=
  .ELet _ _ _ (.EIntLit 1)
    (.ELet _ _ _ (.EPlus (n₁ := 1) (n₂ := 1) _ _ (.EVarRef "x" rfl) (.EIntLit 1))
      (.EPlus (n₁ := 1) (n₂ := 2) _ _ (.EVarRef "x" rfl) (.EVarRef "y" rfl)))

/-- Twice one more than `n`. -/
lgtm private def letDouble as "let-double" (n : int) : int :=
  let m = n + 1 in m + m

#guard letDouble.check []

-- The binding goes in front of the call environment, so a `let` in a declaration's body sees the
-- parameters and the body sees the binding.
example : Decl.Apply letDouble [] [.int 3] (.int 8) :=
  .EApply _ (.cons "n" (.int 3) .nil)
    (.ELet _ _ _ (.EPlus (n₁ := 3) (n₂ := 1) _ _ (.EVarRef "n" rfl) (.EIntLit 1))
      (.EPlus (n₁ := 4) (n₂ := 4) _ _ (.EVarRef "m" rfl) (.EVarRef "m" rfl)))

-- Soundness covers the new form: the declared result type comes back from `letDouble` checking,
-- with nothing said about the value the binding took.
example (v : Value) (h : Decl.Apply letDouble [] [.int 3] v) : v.HasType .int :=
  h.hasType Globals.wellTyped_nil (by simp [letDouble, List.lookup])

/-- What a `let` binds is what its body computes with — here twice over, which is the property the
binding exists to express: `m` is evaluated once and read twice. -/
private theorem letDouble.eq_twice {n : Int} {res : Value}
    (h : Decl.Apply letDouble [] [.int n] res) : res = .int (2 * (n + 1)) := by
  obtain ⟨-, -, hbody⟩ := h
  cases hbody with
  | ELet _ _ _ hm hbody =>
    cases hm with
    | EPlus _ _ h₁ h₂ =>
      cases h₁ with
      | EVarRef _ hln =>
        cases h₂ with
        | EIntLit _ =>
          cases hbody with
          | EPlus _ _ h₃ h₄ =>
            cases h₃ with
            | EVarRef _ hlm =>
              cases h₄ with
              | EVarRef _ hlm' =>
                simp [letDouble, Decl.callEnv, Env.extend, Globals.env, Env.lookup,
                  List.lookup] at hln hlm hlm'
                grind

-- A `let` whose body is a lambda is how a closure captures something other than a parameter: the
-- same closure `~(adderExpr)(10)` returns, reached without a call.
example : Eval ∅ [lgtm| let n = 10 in fun (x : int) => ~(adderInner)]
    (.closure [("n", .int 10)] [] [("x", .int)] adderInner) :=
  .ELet _ _ _ (.EIntLit 10) (.ELam _ _)

-- The bound expression runs in the environment the `let` was reached in, so a `let` is not
-- recursive: `x` on the right of the `=` is the outer `x`, and with no outer `x` it is stuck.
example : Eval ∅ [lgtm| let x = 1 in let x = x + 1 in x] (.int 2) :=
  .ELet _ _ _ (.EIntLit 1)
    (.ELet _ _ _ (.EPlus (n₁ := 1) (n₂ := 1) _ _ (.EVarRef "x" rfl) (.EIntLit 1))
      (.EVarRef "x" rfl))

example (v : Value) : ¬ Eval ∅ [lgtm| let x = x + 1 in x] v := by
  intro h
  cases h with
  | ELet _ _ _ hx _ =>
      cases hx with
      | EPlus _ _ h₁ _ =>
          cases h₁ with
          | EVarRef _ hlx => simp [Env.lookup] at hlx

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

-- A `let` shadows a global the same way a parameter does, so the name becomes a value rather than
-- something to call.
#guard ({ quad with body := [lgtm| let double = n in double] } : Decl).check arith
#guard !({ quad with body := [lgtm| let double = n in double(1)] } : Decl).check arith

-- And `Env.lookup` reads it the same way round: the binding is found before the globals are
-- consulted, so the closure `double` would have resolved to is never built.
example : Decl.Apply { quad with body := [lgtm| let double = n in double] } arith [.int 3]
    (.int 3) :=
  .EApply _ (.cons "n" (.int 3) .nil) (.ELet _ _ _ (.EVarRef "n" rfl) (.EVarRef "double" rfl))

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
