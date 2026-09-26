module

public import LgtmDeepLean.IR
meta import LgtmDeepLean.IR

/-- The types of the variables in scope, innermost binding first. -/
public abbrev Context := List (String × Ty)

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

/-- Check a declaration: its body has to check against the declared result type under the
parameters.

`Decl.parameters` is a `Context`, so a declaration needs no context of its own to be checked in:
the parameters are the only names its body may mention, and they arrive carrying their types. -/
public def Decl.check (d : Decl) : Bool :=
  d.body.check d.parameters d.resultType

/-- `d`'s body agrees with the types `d` declares for its parameters and its result. -/
public def Decl.WellTyped (d : Decl) : Prop :=
  d.check = true

/-- `Decl.check`'s body is not visible outside this module, so this is how a proof elsewhere gets
at what `WellTyped` says: inference on the body finds exactly the declared result type. -/
@[simp, grind =] public theorem Decl.wellTyped_iff_infer_eq_some {d : Decl} :
    d.WellTyped ↔ d.body.infer d.parameters = some d.resultType := by
  simp [Decl.WellTyped, Decl.check, Expression.check]

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
#guard addPred.check
#guard !({ addPred with resultType := .list .int } : Decl).check

-- The parameter list is all the body has to work with, and it is checked at the types it gives.
#guard !({ addPred with parameters := [("x", .int)] } : Decl).check
#guard !({ addPred with parameters := [("x", .int), ("y", .list .int)] } : Decl).check

/-- `fun (s : string) => ["!", s]` -/
private def bang : Decl where
  docstring := "Put `s` after an exclamation mark."
  name := "bang"
  parameters := [("s", .string)]
  body := .lcons (.stringLit "!") (.lcons (.varRef "s") (.lnil .string))
  resultType := .list .string

#guard bang.check
#guard !({ bang with resultType := .list .int } : Decl).check
#guard !({ bang with parameters := [("s", .int)] } : Decl).check

/-- `fun (g : (int) -> int) (x : int) => g(x)` -/
private def applyTo : Decl where
  docstring := "Call `g` on `x`."
  name := "apply-to"
  parameters := [("g", .fn [.int] .int), ("x", .int)]
  body := .app (.varRef "g") [.varRef "x"]
  resultType := .int

-- A parameter of function type is callable, at the arity and types its type gives.
#guard applyTo.check
#guard !({ applyTo with parameters := [("g", .fn [.string] .int), ("x", .int)] } : Decl).check
#guard !({ applyTo with parameters := [("g", .fn [.int, .int] .int), ("x", .int)] } : Decl).check
#guard !({ applyTo with resultType := .string } : Decl).check

/-- `fun (n : int) => fun (m : int) => n + m` -/
private def adder : Decl where
  docstring := "Build a function that adds `n` to its argument."
  name := "adder"
  parameters := [("n", .int)]
  body := .lam [("m", .int)] (.plus (.varRef "n") (.varRef "m"))
  resultType := .fn [.int] .int

-- A declaration can return a function, and its result type is checked like any other.
#guard adder.check
#guard !({ adder with resultType := .int } : Decl).check
#guard !({ adder with resultType := .fn [.string] .int } : Decl).check

end Tests
