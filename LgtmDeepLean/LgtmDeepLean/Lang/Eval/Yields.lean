module

public import LgtmDeepLean.Lang.Eval.Unique

/-! # Constructing an evaluation, form by form

`Eval.unique` says an expression has at most one value, so "`e` evaluates to `v`" and "`e`
evaluates to *exactly* `v`" are the same proposition.  `Eval.Yields` is that proposition read the
second way, and the lemmas below are its composition rules: one per form the model's bodies use —
together with the except forms, which nothing uses yet and which are here so that the first body to
write one is not the thing that has to supply them — each asking for the *facts* that form consumes,
an environment lookup, a field read, the `= some _` answer a partial operation gave, rather than for
derivations of its subexpressions.

This is the forward counterpart of the `Eval.*_inv` family (Eval.lean) and of `Stuck.not_*`
(Progress.lean).  An inversion lemma takes a derivation apart and hands back existentials; a
`Stuck.not_*` lemma refutes a form's failure rules; these *build*, which is what a proof that a
declaration returns something does.  Three things made that expensive when written against the
constructors directly, and each is answered here:

* a rule's conclusion does not determine the values its premises produced, so `Eval.ELet` had to be
  given `v₁` by hand.  A `Yields` hypothesis carries its value, so composing forwards determines it:
  nothing below is left for a caller to guess.
* a rule with a `List.zip` premise asked for one evaluation per element of a list the caller had
  just written out, which came to the same `intro p hp; simp; rcases` ten lines at every call.
  `Eval.YieldsAll` and `Eval.YieldsFields` are those premises as `cons` lists, so an argument list
  is `.cons h₁ (.cons h₂ (.cons h₃ .nil))`.
* the `Stuck.not_*` family asks for hypotheses of the shape `∀ v, Eval td env e v → P v`, because
  when it was written `Eval` was not known to be deterministic.  `Eval.Yields.forall_eval` is what
  collapses those: the value is the one in hand. -/

/-- `Eval.Yields td env e v`: `e` evaluates under `env` to exactly `v`.

`Eval.unique` is what makes "to `v`" and "to exactly `v`" the same proposition, so this is that
relation and nothing more.  What the name carries is a reading rather than content:
`Eval.Yields.forall_eval` is available of every hypothesis of this shape, and a lemma stated over
`Yields` is one whose hypotheses *determine* the values its conclusion mentions, which is what lets
the lemmas below compose forwards.

A `def` rather than an `abbrev`, and exposed rather than opaque, so that it is both: the goals a
progress proof starts from are `Eval`s — `FuncDecl.Apply.EApply` asks for one — and these lemmas
unify with them through the definition, while a goal *left* by one of them keeps `Eval.Yields` as
its head and so takes `.let_`, `.varRef`, `.structGet` by dot notation.  That is most of what a
proof below this layer reads as.  An `abbrev` would unfold on sight and lose the dot notation; a
structure bundling the derivation would cost a projection at every use. -/
@[expose] public def Eval.Yields (td : TypeDecls) (env : Env) (e : Expression) (v : Value) : Prop :=
  Eval td env e v

namespace Eval.Yields

/-- Any value this expression evaluates to is the one in hand.

`Eval.unique` stated the way a caller spends it, which is what every hypothesis of the shape
`∀ v, Eval td env e v → P v` wants: the `Stuck.not_*` family asks for those, and a proof that has a
`Yields` for the subexpression discharges one by `fun u hu => hu ▸ ...` — the quantifier collapses
to the single value. -/
public theorem unique {td : TypeDecls} {env : Env} {e : Expression} {v w : Value}
    (h : Yields td env e v) (h' : Eval td env e w) : w = v :=
  Eval.unique h' h

/-- The same as a function, which is the form a `∀ v, Eval td env e v → P v` hypothesis is proved
by: `fun u hu => by rw [h.forall_eval u hu]; exact ...`. -/
public theorem forall_eval {td : TypeDecls} {env : Env} {e : Expression} {v : Value}
    (h : Yields td env e v) : ∀ u, Eval td env e u → u = v := fun _ hu => Eval.unique hu h

/-! ## Argument and field lists

The premises that run over a `List.zip` — `EApp`'s one evaluation per argument, `EStructNew`'s one
per field — read as `cons` lists instead.  A body writes its argument lists out, so the list is
concrete at every call site and a `cons` list is what a proof of such a premise amounts to; building
one is `.cons h₁ (.cons h₂ .nil)` where the zip form was a `∀ p ∈ ...` to be introduced, simplified
and split case by case.

The lengths come free: a `cons` list cannot pair an argument with nothing, where `List.zip` stops at
the shorter list and the rules have to pin the lengths separately. -/

/-- `YieldsAll td env es vs`: each expression in `es` evaluates to the value at its position in
`vs`, and the two lists are as long as each other. -/
public inductive _root_.Eval.YieldsAll (td : TypeDecls) (env : Env) :
    List Expression → List Value → Prop where
  | nil : YieldsAll td env [] []
  |
  cons {e : Expression} {v : Value} {es : List Expression} {vs : List Value} :
    Yields td env e v → YieldsAll td env es vs → YieldsAll td env (e :: es) (v :: vs)

/-- `YieldsFields td env fes fvs`: each field expression evaluates to the value bound under the same
name in `fvs`, the names being the same in the same order — which is what `EStructNew`'s
`List.map Prod.fst` premise says. -/
public inductive _root_.Eval.YieldsFields (td : TypeDecls) (env : Env) :
    List (FieldName × Expression) → FieldValues → Prop where
  | nil : YieldsFields td env [] []
  |
  cons (f : FieldName) {e : Expression} {v : Value} {fes : List (FieldName × Expression)}
      {fvs : FieldValues} :
    Yields td env e v → YieldsFields td env fes fvs →
      YieldsFields td env ((f, e) :: fes) ((f, v) :: fvs)

end Eval.Yields

namespace Eval.YieldsAll

public theorem length_eq {td : TypeDecls} {env : Env} {es : List Expression} {vs : List Value}
    (h : YieldsAll td env es vs) : es.length = vs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simpa using ih

/-- The `List.zip` premise the rules are stated with, read off the `cons` list. -/
public theorem forall_zip {td : TypeDecls} {env : Env} {es : List Expression} {vs : List Value}
    (h : YieldsAll td env es vs) : ∀ p ∈ es.zip vs, Eval td env p.1 p.2 := by
  induction h with
  | nil => simp
  | cons he _ ih =>
    intro p hp
    rcases List.mem_cons.mp (by simpa using hp) with rfl | hp'
    · exact he
    · exact ih p hp'

end Eval.YieldsAll

namespace Eval.YieldsFields

public theorem map_fst_eq {td : TypeDecls} {env : Env} {fes : List (FieldName × Expression)}
    {fvs : FieldValues} (h : YieldsFields td env fes fvs) :
    fes.map Prod.fst = fvs.map Prod.fst := by
  induction h with
  | nil => rfl
  | cons _ _ _ ih => simpa using ih

public theorem forall_zip {td : TypeDecls} {env : Env} {fes : List (FieldName × Expression)}
    {fvs : FieldValues} (h : YieldsFields td env fes fvs) :
    ∀ p ∈ fes.zip fvs, Eval td env p.1.2 p.2.2 := by
  induction h with
  | nil => simp
  | cons _ he _ ih =>
    intro p hp
    rcases List.mem_cons.mp (by simpa using hp) with rfl | hp'
    · exact he
    · exact ih p hp'

end Eval.YieldsFields

namespace Eval.Yields

/-! ## The forms

One lemma per form, in the order `Eval`'s rules are given.  A form whose value depends on a partial
operation takes that operation's `= some _` answer as a hypothesis — `Value.index? vs n = some w`,
`KeyValues.lookup? kvs vk = some o`, `Value.beq? a b = some b'` — so the caller discharges it from
the model's invariants, which is where that work goes anyway. -/

public theorem varRef {td : TypeDecls} {env : Env} {x : String} {v : Value}
    (hx : env.lookup x = some v) : Yields td env (.varRef x) v := Eval.EVarRef _ hx

public theorem lam {td : TypeDecls} {env : Env} {ps : List (String × Ty)} {body : Expression} :
    Yields td env (.lam ps body) (env.closure ps body) := Eval.ELam _ _

public theorem intLit {td : TypeDecls} {env : Env} {i : Int} :
    Yields td env (.intLit i) (.int i) := Eval.EIntLit _

public theorem stringLit {td : TypeDecls} {env : Env} {s : String} :
    Yields td env (.stringLit s) (.string s) := Eval.EStringLit _

/-- A `let` evaluates what it binds and then its body with that value bound in front.

The bound value comes from `he` rather than being an implicit for the caller to supply, which is
what makes a chain of `let`s a chain of these: `Eval.ELet (v₁ := ...)` had to be told what its own
first premise was going to produce. -/
public theorem let_ {td : TypeDecls} {env : Env} {x : String} {e body : Expression} {w v : Value}
    (he : Yields td env e w)
    (hbody : Yields td ⟨(x, w) :: env.bindings, env.globals⟩ body v) :
    Yields td env (.let_ x e body) v := Eval.ELet _ _ _ he hbody

public theorem structNew {td : TypeDecls} {env : Env} {name : String}
    {fes : List (FieldName × Expression)} {fvs : FieldValues}
    (h : YieldsFields td env fes fvs) : Yields td env (.structNew name fes) (.struct name fvs) :=
  Eval.EStructNew _ _ h.map_fst_eq h.forall_zip

/-- Reading a field off a value that carries it.

The field read is `Value.field?` of the operand's value rather than a lookup in a struct's fields,
which is what the model's own hypotheses are (`selection.field? "thread" = some thread`) and what
keeps the struct's name and field list out of the statement: writing it the other way round left
them as metavariables for the caller to supply by hand at every field read.  That a value
`Value.field?` answers for is a struct value is `Value.isStruct_of_field?`. -/
public theorem structGet {td : TypeDecls} {env : Env} {e : Expression} {v : Value} {f : FieldName}
    {w : Value} (he : Yields td env e v) (hf : v.field? f = some w) :
    Yields td env (.structGet e f) w := by
  obtain ⟨name, fvs, rfl⟩ := Value.isStruct_of_field? hf
  exact Eval.EStructGet _ _ he (by simpa [Value.field?] using hf)

public theorem plus {td : TypeDecls} {env : Env} {e₁ e₂ : Expression} {n₁ n₂ : Int}
    (h₁ : Yields td env e₁ (.int n₁)) (h₂ : Yields td env e₂ (.int n₂)) :
    Yields td env (.plus e₁ e₂) (.int (n₁ + n₂)) := Eval.EPlus _ _ h₁ h₂

public theorem minus {td : TypeDecls} {env : Env} {e₁ e₂ : Expression} {n₁ n₂ : Int}
    (h₁ : Yields td env e₁ (.int n₁)) (h₂ : Yields td env e₂ (.int n₂)) :
    Yields td env (.minus e₁ e₂) (.int (n₁ - n₂)) := Eval.EMinus _ _ h₁ h₂

public theorem min {td : TypeDecls} {env : Env} {e₁ e₂ : Expression} {n₁ n₂ : Int}
    (h₁ : Yields td env e₁ (.int n₁)) (h₂ : Yields td env e₂ (.int n₂)) :
    Yields td env (.min e₁ e₂) (.int (Min.min n₁ n₂)) := Eval.EMin _ _ h₁ h₂

public theorem max {td : TypeDecls} {env : Env} {e₁ e₂ : Expression} {n₁ n₂ : Int}
    (h₁ : Yields td env e₁ (.int n₁)) (h₂ : Yields td env e₂ (.int n₂)) :
    Yields td env (.max e₁ e₂) (.int (Max.max n₁ n₂)) := Eval.EMax _ _ h₁ h₂

/-- A comparison, with the answer `Value.beq?` gave as the hypothesis: that is the premise that
makes a pair it has no answer for stuck, and the one thing a caller has to bring. -/
public theorem equals {td : TypeDecls} {env : Env} {l r : Expression} {v₁ v₂ : Value} {b : Bool}
    (hl : Yields td env l v₁) (hr : Yields td env r v₂) (hb : Value.beq? v₁ v₂ = some b) :
    Yields td env (.equals l r) (.bool b) := Eval.EEquals _ _ hl hr hb

public theorem le {td : TypeDecls} {env : Env} {l r : Expression} {v₁ v₂ : Value} {b : Bool}
    (hl : Yields td env l v₁) (hr : Yields td env r v₂) (hb : Value.le? v₁ v₂ = some b) :
    Yields td env (.le l r) (.bool b) := Eval.ELe _ _ hl hr hb

public theorem lcons {td : TypeDecls} {env : Env} {e₁ e₂ : Expression} {v : Value}
    {vs : List Value} (h₁ : Yields td env e₁ v) (h₂ : Yields td env e₂ (.list vs)) :
    Yields td env (.lcons e₁ e₂) (.list (v :: vs)) := Eval.ECons _ _ h₁ h₂

public theorem lnil {td : TypeDecls} {env : Env} {ty : Ty} :
    Yields td env (.lnil ty) (.list []) := Eval.ENil _

/-- A match on an option that came out holding a value.

Stated of any empty case, which covers the shape the model writes — an `unreachable` there, whose
having no value is what a proof of this is spending its invariants on.  The empty case is never
mentioned, exactly as in `EOptionMatchSome`. -/
public theorem optionMatch_some {td : TypeDecls} {env : Env} {scrut nbody : Expression}
    {x : String} {sbody : Expression} {w v : Value}
    (hscrut : Yields td env scrut (.option (some w)))
    (hbody : Yields td ⟨(x, w) :: env.bindings, env.globals⟩ sbody v) :
    Yields td env (.optionMatch scrut nbody x sbody) v :=
  Eval.EOptionMatchSome _ _ _ _ hscrut hbody

public theorem optionMatch_none {td : TypeDecls} {env : Env} {scrut nbody : Expression}
    {x : String} {sbody : Expression} {v : Value} (hscrut : Yields td env scrut (.option none))
    (hbody : Yields td env nbody v) : Yields td env (.optionMatch scrut nbody x sbody) v :=
  Eval.EOptionMatchNone _ _ _ _ hscrut hbody

/-! The except forms.  The two values are one rule apiece and their annotation goes nowhere, so each
is its operand's `Yields` and nothing else; the match is two rules, and which of them a caller is
building is decided by the half its scrutinee came out carrying. -/

public theorem exceptOk {td : TypeDecls} {env : Env} {ty : Ty} {e : Expression} {v : Value}
    (he : Yields td env e v) : Yields td env (.exceptOk ty e) (.except (.ok v)) :=
  Eval.EOk _ _ he

public theorem exceptError {td : TypeDecls} {env : Env} {ty : Ty} {e : Expression} {v : Value}
    (he : Yields td env e v) : Yields td env (.exceptError ty e) (.except (.error v)) :=
  Eval.EError _ _ he

/-- A match on an except that came out carrying an error, stated of any `ok` case: only one of the
two is ever evaluated, so the case that did not run is not mentioned — exactly as in
`EExceptMatchError`, and as `optionMatch_some` does not mention the empty case. -/
public theorem exceptMatch_error {td : TypeDecls} {env : Env} {scrut : Expression} {x : String}
    {ebody : Expression} {y : String} {obody : Expression} {w v : Value}
    (hscrut : Yields td env scrut (.except (.error w)))
    (hbody : Yields td ⟨(x, w) :: env.bindings, env.globals⟩ ebody v) :
    Yields td env (.exceptMatch scrut x ebody y obody) v :=
  Eval.EExceptMatchError _ _ _ _ _ hscrut hbody

/-- And one that came out carrying a value, which is the same lemma read at the other half. -/
public theorem exceptMatch_ok {td : TypeDecls} {env : Env} {scrut : Expression} {x : String}
    {ebody : Expression} {y : String} {obody : Expression} {w v : Value}
    (hscrut : Yields td env scrut (.except (.ok w)))
    (hbody : Yields td ⟨(y, w) :: env.bindings, env.globals⟩ obody v) :
    Yields td env (.exceptMatch scrut x ebody y obody) v :=
  Eval.EExceptMatchOk _ _ _ _ _ hscrut hbody

public theorem listLength {td : TypeDecls} {env : Env} {e : Expression} {vs : List Value}
    (he : Yields td env e (.list vs)) : Yields td env (.listLength e) (.int (vs.length : Int)) :=
  Eval.EListLength _ he

/-- An index, with the element the position holds as the hypothesis rather than the option
`Value.index?` answered with.

Stated this way because what the caller does with the result is match on it: the value is
`.option (some w)` where the rule leaves `.option (Value.index? vs n)`, so the in-range fact is
spent here rather than by rewriting the goal of the match one form out. -/
public theorem listIndex {td : TypeDecls} {env : Env} {l i : Expression} {vs : List Value}
    {n : Int} {w : Value} (hl : Yields td env l (.list vs)) (hi : Yields td env i (.int n))
    (hw : Value.index? vs n = some w) : Yields td env (.listIndex l i) (.option (some w)) :=
  hw ▸ Eval.EListIndex _ _ hl hi

public theorem hashmapGet {td : TypeDecls} {env : Env} {m k : Expression} {kvs : KeyValues}
    {vk : Value} {o : Option Value} (hm : Yields td env m (.hashmap kvs))
    (hk : Yields td env k vk) (hlookup : KeyValues.lookup? kvs vk = some o) :
    Yields td env (.hashmapGet m k) (.option o) := Eval.EHashmapGet _ _ hm hk hlookup

/-! ### The forms that call a function

One hypothesis per element — or per pair, for a sort by a comparison — with the `ArgsHaveType`
clause and the `Yields` clause bundled into it, the way the `Stuck.not_*` family states them: a
caller proves both from the same facts about the element, so splitting them in two would mean
deriving those facts twice. -/

public theorem listMap {td : TypeDecls} {env : Env} {e f : Expression} {vs vs' : List Value}
    {cb : Bindings} {cg : Globals} {ps : Context} {body : Expression}
    (he : Yields td env e (.list vs)) (hf : Yields td env f (.closure cb cg ps body))
    (hlen : vs.length = vs'.length)
    (hcall : ∀ p ∈ vs.zip vs',
      ArgsHaveType td ps [p.1] ∧ Yields td (Env.extend ⟨cb, cg⟩ ps [p.1]) body p.2) :
    Yields td env (.listMap e f) (.list vs') :=
  Eval.EListMap _ _ he hf hlen (fun p hp => (hcall p hp).1) (fun p hp => (hcall p hp).2)

/-- A flat mapping: a mapping's hypotheses with each call producing a list, which is run together
with the others. -/
public theorem listFlatMap {td : TypeDecls} {env : Env} {e f : Expression} {vs : List Value}
    {vss : List (List Value)} {cb : Bindings} {cg : Globals} {ps : Context} {body : Expression}
    (he : Yields td env e (.list vs)) (hf : Yields td env f (.closure cb cg ps body))
    (hlen : vs.length = vss.length)
    (hcall : ∀ p ∈ vs.zip vss,
      ArgsHaveType td ps [p.1] ∧ Yields td (Env.extend ⟨cb, cg⟩ ps [p.1]) body (.list p.2)) :
    Yields td env (.listFlatMap e f) (.list vss.flatten) :=
  Eval.EListFlatMap _ _ he hf hlen (fun p hp => (hcall p hp).1) (fun p hp => (hcall p hp).2)

/-- A search that found something: the list split at the first element the predicate accepted, which
is what makes the index `pre.length`.

`post` is spoken for by nothing, which is the short circuit the rule carries: the elements after the
match are never handed to the predicate. -/
public theorem listFindIndex_found {td : TypeDecls} {env : Env} {e f : Expression}
    {pre post : List Value} {w : Value} {cb : Bindings} {cg : Globals} {ps : Context}
    {body : Expression} (he : Yields td env e (.list (pre ++ w :: post)))
    (hf : Yields td env f (.closure cb cg ps body))
    (hpre : ∀ u ∈ pre,
      ArgsHaveType td ps [u] ∧ Yields td (Env.extend ⟨cb, cg⟩ ps [u]) body (.bool false))
    (hat : ArgsHaveType td ps [w])
    (hw : Yields td (Env.extend ⟨cb, cg⟩ ps [w]) body (.bool true)) :
    Yields td env (.listFindIndex e f) (.option (some (.int (pre.length : Int)))) :=
  Eval.EListFindIndexSome _ _ he hf (fun u hu => (hpre u hu).1) (fun u hu => (hpre u hu).2) hat hw

/-- And a search that found nothing, which is the one of the two that has to answer for every
element. -/
public theorem listFindIndex_notFound {td : TypeDecls} {env : Env} {e f : Expression}
    {vs : List Value} {cb : Bindings} {cg : Globals} {ps : Context} {body : Expression}
    (he : Yields td env e (.list vs)) (hf : Yields td env f (.closure cb cg ps body))
    (hall : ∀ u ∈ vs,
      ArgsHaveType td ps [u] ∧ Yields td (Env.extend ⟨cb, cg⟩ ps [u]) body (.bool false)) :
    Yields td env (.listFindIndex e f) (.option none) :=
  Eval.EListFindIndexNone _ _ he hf (fun u hu => (hall u hu).1) (fun u hu => (hall u hu).2)

/-- A sort by a comparison, whose hypothesis is over *pairs* of elements: `cmp` is the Lean function
the result is ordered by, and what holds it to the DSL function is the call at every pair the sort
can ask about. -/
public theorem listSortBy {td : TypeDecls} {env : Env} {e f : Expression} {vs : List Value}
    {cmp : Value → Value → Bool} {cb : Bindings} {cg : Globals} {ps : Context} {body : Expression}
    (he : Yields td env e (.list vs)) (hf : Yields td env f (.closure cb cg ps body))
    (hcall : ∀ a ∈ vs, ∀ b ∈ vs, ArgsHaveType td ps [a, b] ∧
      Yields td (Env.extend ⟨cb, cg⟩ ps [a, b]) body (.bool (cmp a b))) :
    Yields td env (.listSortBy e f) (.list (Value.sortWith cmp vs)) :=
  Eval.EListSortBy _ _ he hf (fun a ha b hb => (hcall a ha b hb).1)
    (fun a ha b hb => (hcall a ha b hb).2)

/-! ### Calls

A call to a name the environment binds to a closure, and a call to a name the globals declare.  Both
take the arguments as a `YieldsAll`, so the lengths and the one evaluation per argument come
together; the second is `FuncDecl.eval_app_of_apply` with that premise in place of the zip. -/

public theorem app_closure {td : TypeDecls} {env cenv : Env} {x : String} {ps : Context}
    {fbody : Expression} {args : List Expression} {vs : List Value} {v : Value}
    (hx : env.lookup x = some (cenv.closure ps fbody)) (hargs : YieldsAll td env args vs)
    (hat : ArgsHaveType td ps vs) (hbody : Yields td (Env.extend cenv ps vs) fbody v) :
    Yields td env (.app (.varRef x) args) v :=
  Eval.EApp _ _ (Eval.EVarRef _ hx) hargs.length_eq hargs.forall_zip hat hbody

/-- A call to another declaration: the two lookups are what `Env.lookup` consults, in the order it
consults them, and `happly` is the theorem about that declaration this proof is spending. -/
public theorem app_global {td : TypeDecls} {env : Env} {x : String} {d : FuncDecl}
    {args : List Expression} {vs : List Value} {v : Value}
    (hd : env.globals.lookup x = some d) (hb : env.bindings.lookup x = none)
    (hargs : YieldsAll td env args vs) (happly : d.Apply td env.globals vs v) :
    Yields td env (.app (.varRef x) args) v :=
  FuncDecl.eval_app_of_apply hd hb hargs.length_eq hargs.forall_zip happly

/-! ## Argument lists

A call whose arguments are all `varRef`s is the common case — a body passes what it was given along
— and `args_varRef` is that list in one step, built from one uniform lookup fact.  Where the lookups
come name by name instead, `YieldsAll` built by hand — `.cons (varRef h₁) (.cons (varRef h₂) .nil)`
— is the shorter route, and that is what the model's own calls use.

`eq_of_args` is the direction an *inversion* proof wants, and the one place either is spent: a list
of values identified with the one the arguments yield.  It is stated concretely over `Eval` and
`Yields` rather than over a relation the two lists are pointwise in, for the reason
`List.eq_of_zip_unique` (Eval/Unique.lean) is: the element occurs inside the environment as well as
in the argument position, so higher-order unification cannot solve for the relation metavariable. -/

public theorem args_varRef {td : TypeDecls} {env : Env} {xs : List String} {ws : List Value}
    (hb : ∀ p ∈ xs.zip ws, env.lookup p.1 = some p.2) (hlen : xs.length = ws.length) :
    YieldsAll td env (xs.map Expression.varRef) ws := by
  induction xs generalizing ws with
  | nil =>
    obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    exact .nil
  | cons x xs ih =>
    cases ws with
    | nil => simp at hlen
    | cons w ws =>
      exact .cons (varRef (hb (x, w) (by simp)))
        (ih (fun p hp => hb p (by simp [List.zip_cons_cons, hp])) (by simpa using hlen))

/-- And the same read backwards: a list of values an argument list evaluated to is the list it
yields.

What `FuncDecl.apply_of_eval_app`, `Eval.tupleNew_inv` and the `EApp` case of a `cases` hand back is
a list the caller knows only the length of, together with the zip premise it came with, so a proof
about the call has to identify that list with the values it has in hand.  This is that step, and it
is the one place an inversion proof spends a `YieldsAll`: the argument list is concrete, so the
`cons` list is one hypothesis per argument — an environment lookup apiece where the arguments are
names, which is the common case — and what it replaces is one `Eval.varRef_inv` and one `subst` per
argument on top of destructuring the list by its length.

Stated over `Eval.YieldsAll` rather than over the lookups, so that an argument that is not a bare
name is no obstacle: `Eval.Yields` is available of every form, and the hypothesis is whatever builds
the value that argument has. -/
public theorem eq_of_args {td : TypeDecls} {env : Env} {es : List Expression}
    {vs ws : List Value} (hev : ∀ p ∈ es.zip vs, Eval td env p.1 p.2)
    (hlen : es.length = vs.length) (hws : YieldsAll td env es ws) : vs = ws := by
  induction es generalizing vs ws with
  | nil =>
    cases hws
    exact List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
  | cons e es ih =>
    cases hws with
    | cons hw hrest =>
      cases vs with
      | nil => simp at hlen
      | cons v vs =>
        obtain rfl := hw.unique (hev (e, v) (by simp))
        exact congrArg (v :: ·)
          (ih (fun p hp => hev p (by simp [List.zip_cons_cons, hp])) (by simpa using hlen) hrest)

end Eval.Yields

/-! ## Stepping along a body

The expression in a progress proof's goal is a concrete term, so its head constructor says which
lemma above applies: no search and no backtracking, only the question of which alternative matches.
`yields_step` is that choice, and `yields` repeats it, leaving the side goals a caller has to prove
from the model's invariants — environment lookups, `= some _` facts, and the per-element obligations
of the forms that call a function.

The environment lookups are discharged by one hook, `yields_lookup`, rather than inline at every
alternative: it is `rfl` where the environment is built out of exposed definitions and otherwise
`lgtm_env`, and keeping it in one place is what lets the set behind it be swapped.  Its optional
bracket takes whatever extra facts a lookup needs — `yields_lookup [hthreads]` where the binding
comes from a hypothesis rather than from the environment's own shape. -/

section
open Lean.Parser.Tactic

/-- The discharge hook for a goal about the environment a body runs in: a lookup, the globals table
it carries, or a fact about another declaration transported to it (`yields_lookup using h`).

One place, deliberately — the set behind it is `lgtm_env` and nothing else has to change when that
changes.  `rfl` first, which is what settles a lookup in an environment a call built out of a
declaration's parameters: every definition on the way is exposed, so the lookup computes.
`lgtm_env` behind it is for the ones that do not — a binding that comes from a hypothesis, or an
environment with a variable in it — and the bracket is where those facts go. -/
syntax "yields_lookup" ("[" simpLemma,* "]")? (" using " term)? : tactic

macro_rules
  | `(tactic| yields_lookup) => `(tactic| yields_lookup [])
  | `(tactic| yields_lookup [$ts,*]) =>
    `(tactic| first
      | rfl
      | (simp [lgtm_env, $ts,*] <;> try rfl))
  | `(tactic| yields_lookup using $h) => `(tactic| yields_lookup [] using $h)
  | `(tactic| yields_lookup [$ts,*] using $h) => `(tactic| simpa [lgtm_env, $ts,*] using $h)

/-- One form of the body, built by the lemma its head constructor calls for.

The forms whose value is determined by the environment alone — a name, a lambda, a literal, the
empty list — are finished here, the lookup going to `yields_lookup`; every other alternative leaves
its subexpressions and its side conditions (a field read, a comparison's answer, an index in range)
as goals.

Four kinds of form are left out deliberately.  A call is one: which declaration it reaches and what
that declaration answers is the theorem the proof is spending, not something a step can decide.  The
forms that call a function per element are another: their value is a list the caller has to produce.
And `optionMatch` has two rules, of which this takes the one the model's `unreachable`-on-none shape
needs — a scrutinee that came out empty is a case for the caller to write out.

`exceptMatch` has two rules and neither is taken, which is where it parts company with
`optionMatch`: there, the case the model writes is settled in advance by the `unreachable`, while
either case of an except binds a name and nothing yet says which one a body means.  An alternative
here would commit every match to that half and leave a scrutinee goal no caller in the other half
could discharge, so `Eval.Yields.exceptMatch_error` and `Eval.Yields.exceptMatch_ok` are applied by
name until a shape the model writes makes one of them the default. -/
syntax "yields_step" ("[" simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| yields_step) => `(tactic| yields_step [])
  | `(tactic| yields_step [$ts,*]) =>
    `(tactic| first
      | exact Eval.Yields.varRef (by yields_lookup [$ts,*])
      | exact Eval.Yields.lam
      | exact Eval.Yields.intLit
      | exact Eval.Yields.stringLit
      | exact Eval.Yields.lnil
      | apply Eval.Yields.let_
      | apply Eval.Yields.structGet
      | apply Eval.Yields.structNew
      | apply Eval.Yields.lcons
      | apply Eval.Yields.equals
      | apply Eval.Yields.le
      | apply Eval.Yields.plus
      | apply Eval.Yields.minus
      | apply Eval.Yields.min
      | apply Eval.Yields.max
      | apply Eval.Yields.listLength
      | apply Eval.Yields.listIndex
      | apply Eval.Yields.hashmapGet
      | apply Eval.Yields.optionMatch_some
      | apply Eval.Yields.exceptOk
      | apply Eval.Yields.exceptError
      | apply Eval.YieldsFields.cons
      | exact Eval.YieldsFields.nil
      | apply Eval.YieldsAll.cons
      | exact Eval.YieldsAll.nil)

/-- `yields_step` until no goal takes another: the body read down to the facts the caller owes.

Depth first and in order, so a lookup that determines a value is discharged before the goals that
mention it.  A value no step could determine is left as a goal of its own — `⊢ Value` beside the
`Yields` goal that will settle it — and those disappear as the real goals are proved, which is why
this is for a run of forms rather than for a whole body: a `let` whose bound expression is a call is
better written out, with the derivation of the call where the value can be read off it. -/
syntax "yields" ("[" simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| yields) => `(tactic| yields [])
  | `(tactic| yields [$ts,*]) => `(tactic| repeat' yields_step [$ts,*])

end
