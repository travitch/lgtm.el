module

public import LgtmDeepLean.IR
public import LgtmDeepLean.TypeCheck

public inductive Value where
| int : Int → Value
| list : List Value → Value

/-- The `Ty` a value's representation agrees with.

A list value is homogeneous: every element has the list's single element type. -/
public inductive Value.HasType : Value → Ty → Prop where
| int (i : Int) : HasType (.int i) .int
| list {vs : List Value} {t : Ty} : (∀ v ∈ vs, HasType v t) → HasType (.list vs) (.list t)

public abbrev Env := List (String × Value)

/-- `env` supplies every binding `ctx` promises, at the type `ctx` gives it.

This is the environment-level counterpart of `Value.HasType`: it is what makes a `varRef` safe to
evaluate, and it is the only thing `Eval.hasType` needs to know about an environment. -/
public def Env.HasType (env : Env) (ctx : Context) : Prop :=
  ∀ x t, ctx.lookup x = some t → ∃ v, env.lookup x = some v ∧ v.HasType t

public inductive Eval (env : Env) : Expression → Value → Prop where
| EVarRef (x : String) : env.lookup x = some v → Eval env (.varRef x) v
| EIntLit (i : Int) : Eval env (.intLit i) (.int i)
| EPlus (e₁ : Expression) (e₂ : Expression) : Eval env e₁ (.int n₁) → Eval env e₂ (.int n₂) → Eval env (.plus e₁ e₂) (.int (n₁ + n₂))
| EMinus (e₁ : Expression) (e₂ : Expression) : Eval env e₁ (.int n₁) → Eval env e₂ (.int n₂) → Eval env (.minus e₁ e₂) (.int (n₁ - n₂))
| ENil (ty : Ty) : Eval env (.lnil ty) (.list [])
| ECons (e₁ : Expression) (e₂ : Expression) : Eval env e₁ v → Eval env e₂ (.list vs) → Eval env (.lcons e₁ e₂) (.list (v :: vs))

/-- Evaluating a well-typed expression produces a value of its inferred type.

`ECons` needs no premise relating the new element to the rest of the list: `Expression.infer`
already requires the tail to be a list of the element type read off the head, so the values
`ECons` builds are homogeneous whenever the expression it evaluates is well typed.

`EVarRef` is the one rule that reads a value it did not build, so it is the one rule that needs
`henv`: the type inferred for a variable is the context's, and only `Env.HasType` ties that to the
value the environment hands back. -/
public theorem Eval.hasType {env : Env} {ctx : Context} {e : Expression} {v : Value} {t : Ty}
    (h : Eval env e v) (henv : Env.HasType env ctx) (ht : e.infer ctx = some t) : v.HasType t := by
  induction h generalizing t with
  | EVarRef x hx =>
      obtain ⟨v', hv', hty⟩ := henv x t (by simpa using ht)
      grind
  | ECons e₁ e₂ h₁ h₂ ih₁ ih₂ =>
      obtain ⟨t', ht₁, ht₂, rfl⟩ := Expression.infer_lcons_eq_some.mp ht
      have hv := ih₁ ht₁
      cases ih₂ ht₂ with
      | list hall => exact .list (by grind)
  | _ => grind [Value.HasType]

/-- `ArgsHaveType ps args`: `args` are values a function with parameters `ps` can be called with,
one argument per parameter and each of the type its parameter declares.

Walking the two lists together also pins the arity down: a call passing too few or too many
arguments has no such proof. -/
public inductive Decl.ArgsHaveType : Context → List Value → Prop where
| nil : ArgsHaveType [] []
| cons (x : String) : v.HasType t → ArgsHaveType ps args → ArgsHaveType ((x, t) :: ps) (v :: args)

/-- The environment a call to `d` evaluates its body in: each parameter name bound to its
argument, and nothing else.

`List.lookup` reads the first binding of a name, so a parameter repeated in `d.parameters` takes
the argument of its leftmost occurrence. -/
public def Decl.callEnv (d : Decl) (args : List Value) : Env :=
  (d.parameters.map Prod.fst).zip args

/-- Binding well-typed arguments to their parameters gives an environment the parameter list
describes.

`Decl.parameters` is a `Context`, so this is what lets a call use it as one: the types the
body was written against and the types the arguments arrive with are the same list. -/
public theorem Env.hasType_zip {ps : Context} {args : List Value}
    (h : Decl.ArgsHaveType ps args) : Env.HasType ((ps.map Prod.fst).zip args) ps := by
  induction h with
  | nil => intro x t hx; simp at hx
  | cons _ hv _ ih =>
      intro x t hx
      simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons] at hx ⊢
      split at hx
      · exact ⟨_, rfl, by grind⟩
      · exact ih x t hx

/-- `Apply d args v`: calling `d` with `args` returns `v`.

A call binds the parameters to the arguments positionally and evaluates the body under those
bindings and nothing else, so a body mentioning any other name has no value.

The `ArgsHaveType` premise is what makes a call with the wrong arguments stuck rather than junk:
arguments of the wrong type, or the wrong number of them, produce no value at all.  It is also
all `Apply.hasType` needs to read `d.parameters` as the context the body was checked in. -/
public inductive Decl.Apply (d : Decl) : List Value → Value → Prop where
| EApply (args : List Value) :
    Decl.ArgsHaveType d.parameters args → Eval (d.callEnv args) d.body v → Apply d args v

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

end Tests
