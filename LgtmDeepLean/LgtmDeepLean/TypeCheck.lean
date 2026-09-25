module

public import LgtmDeepLean.IR
meta import LgtmDeepLean.IR

/-- The types of the variables in scope, innermost binding first. -/
public abbrev Context := List (String × Ty)

/-- Infer the type of `e` under `ctx`, or `none` if `e` is ill typed.

Every form determines its own type: `lnil` carries the element type of the empty list it builds,
so inference never has to guess and needs no expected type to work from.  `Expression.check` is
therefore just this function plus a comparison. -/
public def Expression.infer (ctx : Context) : Expression → Option Ty
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

private def ctx : Context := [("xs", .list .int), ("n", .int), ("s", .string)]

-- Inference determines the type of every form.
#guard (Expression.intLit 3).infer ctx == some .int
#guard (Expression.stringLit "hi").infer ctx == some .string
#guard (Expression.varRef "n").infer ctx == some .int
#guard (Expression.varRef "s").infer ctx == some .string
#guard (Expression.varRef "xs").infer ctx == some (.list .int)
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

-- Checking agrees with inference.
#guard (Expression.lnil .int).check ctx (.list .int)
#guard !(Expression.lnil .int).check ctx .int
#guard (Expression.plus (.varRef "n") (.intLit 1)).check ctx .int
#guard !(Expression.plus (.varRef "n") (.intLit 1)).check ctx (.list .int)
#guard !(Expression.plus (.varRef "n") (.lnil .int)).check ctx .int
#guard (Expression.stringLit "hi").check ctx .string
#guard !(Expression.stringLit "hi").check ctx .int

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

end Tests
