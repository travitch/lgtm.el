module

public import LgtmDeepLean.Lang.Eval
public import LgtmDeepLean.Lang.Eval.Unique

/-! # Going wrong

`Eval.hasType` is preservation: an expression that has a value and a type has a value *of* that
type.  Progress is the other half — that a well-typed expression is never stopped by its own
ill-formedness — and in a big-step semantics it cannot be stated as "a well-typed expression has a
value".  Two things that are nothing to do with typing already make that false:

* a global may call itself, so a body may diverge, and a relational big-step evaluator says nothing
  about the difference between diverging and going wrong — both are `¬∃ v, Eval td env e v`;
* `Expression.unreachable` has no rule by design (`Eval.not_unreachable`), so an expression reaching
  one has no value however well typed it is.  That is the whole point of the form.

So progress is stated negatively instead, over a relation that says what *going wrong* is.  `Stuck
td env e` holds when evaluating `e` under `env` reaches a form that no rule of `Eval` can fire on —
a condition that is not a `bool`, a field the value does not carry, a match with no alternative for
the constructor it was handed.  Progress is then `¬Stuck`, and divergence and `unreachable` cost it
nothing: neither is a derivation of this relation.

## How the rules are arrived at

One recipe, applied to each rule of `Eval` in turn.  Reading a rule's premises left to right, each
one either evaluates a subexpression or asks something of a value an earlier premise produced, and
each gives a rule here:

* *propagation* — a subexpression that must be evaluated is itself stuck.  `iteCond` is `ite`'s, and
  `iteThen` and `iteElse` are the two a conditional needs instead of one, since which branch is
  evaluated depends on the condition's value.  A subexpression no evaluation reaches contributes no
  rule: nothing here mentions the branch a conditional did not take, exactly as `Eval` mentions
  neither.
* *mismatch* — every subexpression evaluated, and what came back is not what the rule matches on.
  `iteNotBool` is `ite`'s, and `Value.IsBool` and its eight neighbours below are what those rules
  negate.

A rule of `Eval` whose premises are all evaluations and whose result is built by a function
therefore has propagation rules and no mismatch rule: `structNew`, `indNew` and `tupleNew` are
stuck only where a field, an argument or an element is, and `lam`, the literals, `lnil`,
`optionNone` and `hashmapEmpty` are never stuck at all.

Two rules are deliberately *not* here.  `Expression.unreachable` is the first, for the reason it has
no rule in `Eval`: reaching one is something a proof rules out, not something the type checker did.
And nothing says a struct update that names a field the struct does not have is stuck —
`FieldValues.update` drops it and the update has a value, so that is an ill-typed expression with
the wrong answer rather than no answer.

## What this is for

`Progress` below is the theorem the relation exists to state, and writing the relation down is what
found the one place the language went wrong: `Value.beqFields?` compared two struct values' fields
positionally, so two values of one struct type built with their fields in different orders had no
comparison at all.  It matches fields by name now, and `Stuck.eval_pairEquals` is the pair that used
to be stuck.

What a proof of the theorem still needs is canonical forms for `Value.HasType`, `ArgsHaveType`
rebuilt from the argument types, and the totality of the two comparisons on the types their forms
insist on.  `Value.cmp?` on a `Ty.orderable` type is in reach; `Value.beq?` on a `Ty.comparable` one
rests on `TypeDecls.budget` being enough fuel to walk the declarations, which nothing has proved. -/

/-- `Stuck td env e`: evaluating `e` under `env` reaches a form no rule of `Eval` can fire on.

This is the relation progress is stated over, and it is `Eval` read for failure: see the module
docstring for the recipe that produced the rules, and `Stuck.not_unreachable` for the one form that
is stuck in `Eval` and absent here. -/
public inductive Stuck (td : TypeDecls) : Env → Expression → Prop where
  /-- A call evaluates its function, then its arguments, then the body under them, so it is stuck
wherever any of those is.  Between them is the one failure a call has of its own: arguments that do
not fit the closure's parameters, which is `ArgsHaveType` and so covers the wrong number of them as
well as the wrong types. -/
  | appFn : Stuck td env f → Stuck td env (.app f args)
  | appFnNotClosure : Eval td env f v → ¬v.IsClosure → Stuck td env (.app f args)
  | appArg {args : List Expression} {arg : Expression} :
    arg ∈ args → Stuck td env arg → Stuck td env (.app f args)
  |
  appArgs :
    Eval td env f (.closure cbindings cglobals ps body) →
      args.length = vs.length →
      (∀ p ∈ args.zip vs, Eval td env p.1 p.2) → ¬ArgsHaveType td ps vs → Stuck td env (.app f args)
  /-- The body of the function, under the bindings the call made: where a call diverges, and the one
rule here that says nothing about the expression it is a rule for. -/
  |
  appBody :
    Eval td env f (.closure cbindings cglobals ps body) →
      args.length = vs.length →
      (∀ p ∈ args.zip vs, Eval td env p.1 p.2) →
      ArgsHaveType td ps vs →
      Stuck td (Env.extend ⟨cbindings, cglobals⟩ ps vs) body → Stuck td env (.app f args)
  /-- A conditional is stuck in its condition, on a condition that is not a `bool`, or in the branch
the condition chose.  Two branch rules rather than one, as `Eval` has two rules rather than one: the
branch that did not run is not mentioned, so a conditional guarding an unevaluable branch with a
condition that never chooses it is not stuck. -/
  | iteCond : Stuck td env c → Stuck td env (.ite c thn els)
  | iteNotBool : Eval td env c v → ¬v.IsBool → Stuck td env (.ite c thn els)
  | iteThen : Eval td env c (.bool true) → Stuck td env thn → Stuck td env (.ite c thn els)
  | iteElse : Eval td env c (.bool false) → Stuck td env els → Stuck td env (.ite c thn els)
  /-- A conjunction is stuck in its left operand, on a left operand that is not a `bool`, or — only
where that operand came out `true` — in its right operand or on a right operand that is not a
`bool`.  A `false` on the left settles the result, so nothing about the right operand can stop it,
which is the short-circuit read as a failure. -/
  | boolAndLeft : Stuck td env l → Stuck td env (.boolAnd l r)
  | boolAndLeftNotBool : Eval td env l v → ¬v.IsBool → Stuck td env (.boolAnd l r)
  | boolAndRight : Eval td env l (.bool true) → Stuck td env r → Stuck td env (.boolAnd l r)
  |
  boolAndRightNotBool :
    Eval td env l (.bool true) → Eval td env r v → ¬v.IsBool → Stuck td env (.boolAnd l r)
  /-- A disjunction is the same relation with the short circuit the other way round: a `true` on the
left settles it, so the right operand is reached only from a `false`. -/
  | boolOrLeft : Stuck td env l → Stuck td env (.boolOr l r)
  | boolOrLeftNotBool : Eval td env l v → ¬v.IsBool → Stuck td env (.boolOr l r)
  | boolOrRight : Eval td env l (.bool false) → Stuck td env r → Stuck td env (.boolOr l r)
  |
  boolOrRightNotBool :
    Eval td env l (.bool false) → Eval td env r v → ¬v.IsBool → Stuck td env (.boolOr l r)
  /-- A comparison is stuck in either operand — both are always evaluated, so neither rule mentions
the other operand — or on a pair of values `Value.beq?` has no answer for.  That is a closure on
either side, or two values that disagree about the type they carry, and `Ty.comparable` is the type
checker's side of it. -/
  | equalsLeft : Stuck td env l → Stuck td env (.equals l r)
  | equalsRight : Stuck td env r → Stuck td env (.equals l r)
  |
  equalsIncomparable :
    Eval td env l v₁ → Eval td env r v₂ → Value.beq? v₁ v₂ = none → Stuck td env (.equals l r)
  /-- An ordering is the same three rules with `Value.lt?` in place of `Value.beq?`, and
`Ty.orderable` is what rules the third out. -/
  | ltLeft : Stuck td env l → Stuck td env (.lt l r)
  | ltRight : Stuck td env r → Stuck td env (.lt l r)
  |
  ltIncomparable :
    Eval td env l v₁ → Eval td env r v₂ → Value.lt? v₁ v₂ = none → Stuck td env (.lt l r)
  | leLeft : Stuck td env l → Stuck td env (.le l r)
  | leRight : Stuck td env r → Stuck td env (.le l r)
  |
  leIncomparable :
    Eval td env l v₁ → Eval td env r v₂ → Value.le? v₁ v₂ = none → Stuck td env (.le l r)
  /-- A `let` is stuck in what it binds, or in its body under that binding. -/
  | letBound : Stuck td env e → Stuck td env (.let_ x e body)
  |
  letBody :
    Eval td env e v₁ →
      Stuck td ⟨(x, v₁) :: env.bindings, env.globals⟩ body → Stuck td env (.let_ x e body)
  /-- A name neither the bindings nor the globals supply.  This is the only rule with no premise
about a subexpression, because a `varRef` has none: it is stuck or it is a value. -/
  | varRefUnbound : env.lookup x = none → Stuck td env (.varRef x)
  /-- Building a struct is stuck exactly where one of its fields is.  There is no mismatch rule:
every field that has a value gives the value its name, and the struct is those fields — which is
also why a `structNew` naming fields the declaration does not have is ill typed rather than
stuck. -/
  |
  structNewField {fes : List (FieldName × Expression)} {p : FieldName × Expression} :
    p ∈ fes → Stuck td env p.2 → Stuck td env (.structNew name fes)
  /-- Reading a field is stuck in its operand, on an operand that is not a struct value, or on a
struct value that does not carry the field.  The field is looked up in the *value*, so this last is
a fact about what was built rather than about what was declared. -/
  | structGetOperand : Stuck td env e → Stuck td env (.structGet e f)
  | structGetNotStruct : Eval td env e v → ¬v.IsStruct → Stuck td env (.structGet e f)
  |
  structGetMissing :
    Eval td env e (.struct name fvs) → fvs.lookup f = none → Stuck td env (.structGet e f)
  /-- An update is stuck in its operand, on an operand that is not a struct value, or in one of the
expressions it rebinds a field with.  A field it names that the struct does not have is not one of
them: `FieldValues.update` drops it, so such an update has a value — the wrong one, which is what
typing rules out rather than what this relation describes. -/
  | structUpdateOperand : Stuck td env e → Stuck td env (.structUpdate e fes)
  | structUpdateNotStruct : Eval td env e v → ¬v.IsStruct → Stuck td env (.structUpdate e fes)
  |
  structUpdateField {fes : List (FieldName × Expression)} {p : FieldName × Expression} :
    p ∈ fes → Stuck td env p.2 → Stuck td env (.structUpdate e fes)
  /-- Applying a constructor is stuck exactly where one of its arguments is, the way building a
struct is stuck where one of its fields is, and for the same reason. -/
  |
  indNewArg {args : List Expression} {arg : Expression} :
    arg ∈ args → Stuck td env arg → Stuck td env (.indNew name c args)
  /-- A match is stuck in its scrutinee, on a scrutinee that is not a value of an inductive type, on
a value whose constructor no alternative names, or in the alternative that was chosen.  The third is
non-exhaustiveness, which is what the type checker insists on; the alternative is found by name, so
nothing here depends on where the declaration or the match put it. -/
  | indMatchScrut : Stuck td env scrut → Stuck td env (.indMatch scrut alts)
  | indMatchNotInd : Eval td env scrut v → ¬v.IsInd → Stuck td env (.indMatch scrut alts)
  |
  indMatchNoAlt :
    Eval td env scrut (.ind name c vs) →
      alts.lookup c = none → Stuck td env (.indMatch scrut alts)
  |
  indMatchBody :
    Eval td env scrut (.ind name c vs) →
      alts.lookup c = some (xs, body) →
      Stuck td ⟨xs.zip vs ++ env.bindings, env.globals⟩ body → Stuck td env (.indMatch scrut alts)
  /-- Arithmetic is stuck in either operand or on either operand that is not an `int`.  Both are
always evaluated, so all four rules mention one operand only. -/
  | plusLeft : Stuck td env e₁ → Stuck td env (.plus e₁ e₂)
  | plusLeftNotInt : Eval td env e₁ v → ¬v.IsInt → Stuck td env (.plus e₁ e₂)
  | plusRight : Stuck td env e₂ → Stuck td env (.plus e₁ e₂)
  | plusRightNotInt : Eval td env e₂ v → ¬v.IsInt → Stuck td env (.plus e₁ e₂)
  | minusLeft : Stuck td env e₁ → Stuck td env (.minus e₁ e₂)
  | minusLeftNotInt : Eval td env e₁ v → ¬v.IsInt → Stuck td env (.minus e₁ e₂)
  | minusRight : Stuck td env e₂ → Stuck td env (.minus e₁ e₂)
  | minusRightNotInt : Eval td env e₂ v → ¬v.IsInt → Stuck td env (.minus e₁ e₂)
  /-- A minimum and a maximum are stuck exactly where arithmetic is, and for the same reason: both
operands are evaluated and an `int` is asked of each. -/
  | minLeft : Stuck td env e₁ → Stuck td env (.min e₁ e₂)
  | minLeftNotInt : Eval td env e₁ v → ¬v.IsInt → Stuck td env (.min e₁ e₂)
  | minRight : Stuck td env e₂ → Stuck td env (.min e₁ e₂)
  | minRightNotInt : Eval td env e₂ v → ¬v.IsInt → Stuck td env (.min e₁ e₂)
  | maxLeft : Stuck td env e₁ → Stuck td env (.max e₁ e₂)
  | maxLeftNotInt : Eval td env e₁ v → ¬v.IsInt → Stuck td env (.max e₁ e₂)
  | maxRight : Stuck td env e₂ → Stuck td env (.max e₁ e₂)
  | maxRightNotInt : Eval td env e₂ v → ¬v.IsInt → Stuck td env (.max e₁ e₂)
  /-- An option holding a value is stuck exactly where that value is.  An empty one is never
stuck. -/
  | optionSomeInner : Stuck td env e → Stuck td env (.optionSome e)
  /-- A match on an option is stuck in its scrutinee, on a scrutinee that is not an option, or in
the case the scrutinee chose.  There is no rule for an option whose case is missing, where
`indMatchNoAlt` is one: an option has two cases and the form carries both. -/
  | optionMatchScrut : Stuck td env scrut → Stuck td env (.optionMatch scrut nbody x sbody)
  |
  optionMatchNotOption :
    Eval td env scrut v → ¬v.IsOption → Stuck td env (.optionMatch scrut nbody x sbody)
  |
  optionMatchNone :
    Eval td env scrut (.option none) →
      Stuck td env nbody → Stuck td env (.optionMatch scrut nbody x sbody)
  |
  optionMatchSome :
    Eval td env scrut (.option (some w)) →
      Stuck td ⟨(x, w) :: env.bindings, env.globals⟩ sbody →
      Stuck td env (.optionMatch scrut nbody x sbody)
  /-- A cons is stuck in either operand, or on a tail that is not a list.  Nothing is asked of the
head: a list's element type is whatever the head turned out to be. -/
  | lconsHead : Stuck td env e₁ → Stuck td env (.lcons e₁ e₂)
  | lconsTail : Stuck td env e₂ → Stuck td env (.lcons e₁ e₂)
  | lconsTailNotList : Eval td env e₂ v → ¬v.IsList → Stuck td env (.lcons e₁ e₂)
  /-- A match on a list is stuck in its scrutinee, on a scrutinee that is not a list, or in the case
the scrutinee chose.  A match on an option's four rules with `Value.IsList` in place of
`Value.IsOption`: a list has two cases and the form carries both, so there is no rule for a case that
is missing, and the empty list is a value like any other rather than a failure.  What the non-empty
case adds is the second name in the environment its body is stuck under. -/
  | listMatchScrut : Stuck td env scrut → Stuck td env (.listMatch scrut nbody hd tl cbody)
  |
  listMatchNotList :
    Eval td env scrut v → ¬v.IsList → Stuck td env (.listMatch scrut nbody hd tl cbody)
  |
  listMatchNil :
    Eval td env scrut (.list []) →
      Stuck td env nbody → Stuck td env (.listMatch scrut nbody hd tl cbody)
  |
  listMatchCons :
    Eval td env scrut (.list (w :: ws)) →
      Stuck td ⟨(hd, w) :: (tl, .list ws) :: env.bindings, env.globals⟩ cbody →
      Stuck td env (.listMatch scrut nbody hd tl cbody)
  /-- An index is stuck in either operand, on a first operand that is not a list, or on a second that
is not an `int`.  Both are always evaluated, so each of the four rules mentions one operand only.

An index the list has no element at is not among the failures: that is the empty option, which is a
value like any other — the same thing a key the map does not bind is to `hashmapGet`.  And where a get
has a fifth rule for a lookup with no answer, this has none: `Value.index?` compares nothing, so there
is no `Ty.comparable` for its typing rule to impose and nothing for it to give up on. -/
  | listIndexOperand : Stuck td env l → Stuck td env (.listIndex l i)
  | listIndexNotList : Eval td env l v → ¬v.IsList → Stuck td env (.listIndex l i)
  | listIndexIndex : Stuck td env i → Stuck td env (.listIndex l i)
  | listIndexIndexNotInt : Eval td env i v → ¬v.IsInt → Stuck td env (.listIndex l i)
  /-- A mapping is stuck in either operand, on an operand of the wrong shape, or in one of the calls
it makes: an element that does not fit the closure's parameter — a function of the wrong arity among
them — or a call whose body is stuck.

The call rules speak of one element rather than of the whole list, which is where they part company
with `Eval`'s premises over the zip: a mapping is stuck as soon as one call is, and which element
that was is the whole of what has to be said. -/
  | listMapOperand : Stuck td env e → Stuck td env (.listMap e f)
  | listMapNotList : Eval td env e v → ¬v.IsList → Stuck td env (.listMap e f)
  | listMapFn : Stuck td env f → Stuck td env (.listMap e f)
  | listMapFnNotClosure : Eval td env f v → ¬v.IsClosure → Stuck td env (.listMap e f)
  |
  listMapArg :
    Eval td env e (.list vs) →
      Eval td env f (.closure cbindings cglobals ps body) →
      w ∈ vs → ¬ArgsHaveType td ps [w] → Stuck td env (.listMap e f)
  |
  listMapCall :
    Eval td env e (.list vs) →
      Eval td env f (.closure cbindings cglobals ps body) →
      w ∈ vs →
      ArgsHaveType td ps [w] →
      Stuck td (Env.extend ⟨cbindings, cglobals⟩ ps [w]) body → Stuck td env (.listMap e f)
  /-- A flat mapping is a mapping's six rules and one more: a call that produced something other
than a list, which is the one thing it asks of what its function returned. -/
  | listFlatMapOperand : Stuck td env e → Stuck td env (.listFlatMap e f)
  | listFlatMapNotList : Eval td env e v → ¬v.IsList → Stuck td env (.listFlatMap e f)
  | listFlatMapFn : Stuck td env f → Stuck td env (.listFlatMap e f)
  | listFlatMapFnNotClosure : Eval td env f v → ¬v.IsClosure → Stuck td env (.listFlatMap e f)
  |
  listFlatMapArg :
    Eval td env e (.list vs) →
      Eval td env f (.closure cbindings cglobals ps body) →
      w ∈ vs → ¬ArgsHaveType td ps [w] → Stuck td env (.listFlatMap e f)
  |
  listFlatMapCall :
    Eval td env e (.list vs) →
      Eval td env f (.closure cbindings cglobals ps body) →
      w ∈ vs →
      ArgsHaveType td ps [w] →
      Stuck td (Env.extend ⟨cbindings, cglobals⟩ ps [w]) body → Stuck td env (.listFlatMap e f)
  |
  listFlatMapCallNotList :
    Eval td env e (.list vs) →
      Eval td env f (.closure cbindings cglobals ps body) →
      w ∈ vs →
      ArgsHaveType td ps [w] →
      Eval td (Env.extend ⟨cbindings, cglobals⟩ ps [w]) body w' →
      ¬w'.IsList → Stuck td env (.listFlatMap e f)
  /-- A length and a reversal are stuck in their operand or on an operand that is not a list, and
that is all either of them can be: neither looks at an element. -/
  | listLengthOperand : Stuck td env e → Stuck td env (.listLength e)
  | listLengthNotList : Eval td env e v → ¬v.IsList → Stuck td env (.listLength e)
  /-- A search is a mapping's six rules with an answer that is not a `bool` for a seventh — which is
`listSortBy`'s seventh, since both hold their function to a `bool` — and with the elements its calls
are made about the ones it reaches rather than all of them.

That is what `pre` is for in the last three rules.  A search stops at the first element the predicate
accepts, so an element is handed to it only when every element before that one answered `false`, and
the rules say so: an element the search never reaches contributes no way to be stuck, exactly as the
branch a conditional did not take contributes none.  Everywhere else a call per element is made about
every element, so `w ∈ vs` is all those rules need.

A list the predicate accepts nothing in is not among the failures.  That is the empty option, which
is a value like any other — the same thing a key the map does not bind is to `hashmapGet`. -/
  | listFindIndexOperand : Stuck td env e → Stuck td env (.listFindIndex e f)
  | listFindIndexNotList : Eval td env e v → ¬v.IsList → Stuck td env (.listFindIndex e f)
  | listFindIndexFn : Stuck td env f → Stuck td env (.listFindIndex e f)
  | listFindIndexFnNotClosure : Eval td env f v → ¬v.IsClosure → Stuck td env (.listFindIndex e f)
  |
  listFindIndexArg :
    Eval td env e (.list (pre ++ w :: post)) →
      Eval td env f (.closure cbindings cglobals ps body) →
      (∀ u ∈ pre, ArgsHaveType td ps [u]) →
      (∀ u ∈ pre, Eval td (Env.extend ⟨cbindings, cglobals⟩ ps [u]) body (.bool false)) →
      ¬ArgsHaveType td ps [w] → Stuck td env (.listFindIndex e f)
  |
  listFindIndexCall :
    Eval td env e (.list (pre ++ w :: post)) →
      Eval td env f (.closure cbindings cglobals ps body) →
      (∀ u ∈ pre, ArgsHaveType td ps [u]) →
      (∀ u ∈ pre, Eval td (Env.extend ⟨cbindings, cglobals⟩ ps [u]) body (.bool false)) →
      ArgsHaveType td ps [w] →
      Stuck td (Env.extend ⟨cbindings, cglobals⟩ ps [w]) body → Stuck td env (.listFindIndex e f)
  |
  listFindIndexCallNotBool :
    Eval td env e (.list (pre ++ w :: post)) →
      Eval td env f (.closure cbindings cglobals ps body) →
      (∀ u ∈ pre, ArgsHaveType td ps [u]) →
      (∀ u ∈ pre, Eval td (Env.extend ⟨cbindings, cglobals⟩ ps [u]) body (.bool false)) →
      ArgsHaveType td ps [w] →
      Eval td (Env.extend ⟨cbindings, cglobals⟩ ps [w]) body w' →
      ¬w'.IsBool → Stuck td env (.listFindIndex e f)
  | listReverseOperand : Stuck td env e → Stuck td env (.listReverse e)
  | listReverseNotList : Eval td env e v → ¬v.IsList → Stuck td env (.listReverse e)
  /-- A sort by a key is a mapping's six rules with a seventh for the ordering: two keys the
projection produced that `Value.cmp?` has no answer for, which is what `Ty.orderable` on the
projection's result type rules out.

The seventh rule is over two elements and the keys their calls produced, rather than over the whole
list of keys the way `Eval`'s premise is: a sort is stuck as soon as one pair of keys cannot be
compared. -/
  | listSortOnOperand : Stuck td env e → Stuck td env (.listSortOn e f)
  | listSortOnNotList : Eval td env e v → ¬v.IsList → Stuck td env (.listSortOn e f)
  | listSortOnFn : Stuck td env f → Stuck td env (.listSortOn e f)
  | listSortOnFnNotClosure : Eval td env f v → ¬v.IsClosure → Stuck td env (.listSortOn e f)
  |
  listSortOnArg :
    Eval td env e (.list vs) →
      Eval td env f (.closure cbindings cglobals ps body) →
      w ∈ vs → ¬ArgsHaveType td ps [w] → Stuck td env (.listSortOn e f)
  |
  listSortOnCall :
    Eval td env e (.list vs) →
      Eval td env f (.closure cbindings cglobals ps body) →
      w ∈ vs →
      ArgsHaveType td ps [w] →
      Stuck td (Env.extend ⟨cbindings, cglobals⟩ ps [w]) body → Stuck td env (.listSortOn e f)
  |
  listSortOnKeys :
    Eval td env e (.list vs) →
      Eval td env f (.closure cbindings cglobals ps body) →
      a ∈ vs →
      b ∈ vs →
      ArgsHaveType td ps [a] →
      ArgsHaveType td ps [b] →
      Eval td (Env.extend ⟨cbindings, cglobals⟩ ps [a]) body ka →
      Eval td (Env.extend ⟨cbindings, cglobals⟩ ps [b]) body kb →
      Value.cmp? ka kb = none → Stuck td env (.listSortOn e f)
  /-- A sort by a comparison is the same shape with the calls taking two elements rather than one,
and with the ordering asked of the comparison rather than of a key: an answer that is not a `bool`
is where it is stuck, in place of a pair of keys with no comparison.

So there is no rule here corresponding to `listSortOnKeys` — nothing is compared but what the
comparison answered — which is `Ty.orderable` not appearing in this form's typing rule read as a
failure. -/
  | listSortByOperand : Stuck td env e → Stuck td env (.listSortBy e f)
  | listSortByNotList : Eval td env e v → ¬v.IsList → Stuck td env (.listSortBy e f)
  | listSortByFn : Stuck td env f → Stuck td env (.listSortBy e f)
  | listSortByFnNotClosure : Eval td env f v → ¬v.IsClosure → Stuck td env (.listSortBy e f)
  |
  listSortByArgs :
    Eval td env e (.list vs) →
      Eval td env f (.closure cbindings cglobals ps body) →
      a ∈ vs → b ∈ vs → ¬ArgsHaveType td ps [a, b] → Stuck td env (.listSortBy e f)
  |
  listSortByCall :
    Eval td env e (.list vs) →
      Eval td env f (.closure cbindings cglobals ps body) →
      a ∈ vs →
      b ∈ vs →
      ArgsHaveType td ps [a, b] →
      Stuck td (Env.extend ⟨cbindings, cglobals⟩ ps [a, b]) body → Stuck td env (.listSortBy e f)
  |
  listSortByCallNotBool :
    Eval td env e (.list vs) →
      Eval td env f (.closure cbindings cglobals ps body) →
      a ∈ vs →
      b ∈ vs →
      ArgsHaveType td ps [a, b] →
      Eval td (Env.extend ⟨cbindings, cglobals⟩ ps [a, b]) body w →
      ¬w.IsBool → Stuck td env (.listSortBy e f)
  /-- A put is stuck in any of its three operands, on a first operand that is not a hashmap, or on a
key the map carries that the new key cannot be compared with — which is `KeyValues.erase?` having no
answer, and what `Ty.comparable` on the key type rules out.  All three operands are always
evaluated, so the three propagation rules mention nothing but their own. -/
  | hashmapPutMap : Stuck td env m → Stuck td env (.hashmapPut m k v)
  | hashmapPutMapNotHashmap : Eval td env m w → ¬w.IsHashmap → Stuck td env (.hashmapPut m k v)
  | hashmapPutKey : Stuck td env k → Stuck td env (.hashmapPut m k v)
  | hashmapPutValue : Stuck td env v → Stuck td env (.hashmapPut m k v)
  |
  hashmapPutIncomparable :
    Eval td env m (.hashmap kvs) →
      Eval td env k vk → KeyValues.erase? kvs vk = none → Stuck td env (.hashmapPut m k v)
  /-- A get is the same, one operand fewer, with `KeyValues.lookup?` in place of
`KeyValues.erase?`.  A key the map does not bind is not among the failures: that is the empty
option, which is a value like any other. -/
  | hashmapGetMap : Stuck td env m → Stuck td env (.hashmapGet m k)
  | hashmapGetMapNotHashmap : Eval td env m w → ¬w.IsHashmap → Stuck td env (.hashmapGet m k)
  | hashmapGetKey : Stuck td env k → Stuck td env (.hashmapGet m k)
  |
  hashmapGetIncomparable :
    Eval td env m (.hashmap kvs) →
      Eval td env k vk → KeyValues.lookup? kvs vk = none → Stuck td env (.hashmapGet m k)
  /-- A mapping over a hashmap is a mapping over a list's six rules with the calls taking a binding
— the key beside the value it is bound to — as their two arguments.  Nothing is compared, so there
is no `KeyValues` rule here: a mapping rebinds no key. -/
  | hashmapMapMap : Stuck td env m → Stuck td env (.hashmapMap m f)
  | hashmapMapMapNotHashmap : Eval td env m w → ¬w.IsHashmap → Stuck td env (.hashmapMap m f)
  | hashmapMapFn : Stuck td env f → Stuck td env (.hashmapMap m f)
  | hashmapMapFnNotClosure : Eval td env f w → ¬w.IsClosure → Stuck td env (.hashmapMap m f)
  |
  hashmapMapArgs {kvs : KeyValues} {q : Value × Value} :
    Eval td env m (.hashmap kvs) →
      Eval td env f (.closure cbindings cglobals ps body) →
      q ∈ kvs → ¬ArgsHaveType td ps [q.1, q.2] → Stuck td env (.hashmapMap m f)
  |
  hashmapMapCall {kvs : KeyValues} {q : Value × Value} :
    Eval td env m (.hashmap kvs) →
      Eval td env f (.closure cbindings cglobals ps body) →
      q ∈ kvs →
      ArgsHaveType td ps [q.1, q.2] →
      Stuck td (Env.extend ⟨cbindings, cglobals⟩ ps [q.1, q.2]) body →
      Stuck td env (.hashmapMap m f)
  /-- A conversion is stuck in its operand or on an operand that is not a hashmap, and that is all:
the bindings are already the list it hands back. -/
  | hashmapToListOperand : Stuck td env m → Stuck td env (.hashmapToList m)
  | hashmapToListNotHashmap : Eval td env m w → ¬w.IsHashmap → Stuck td env (.hashmapToList m)
  /-- Building a tuple is stuck exactly where one of its elements is.  How many elements there are
is not checked against anything, so there is nothing else it could be. -/
  |
  tupleNewElem {es : List Expression} {e : Expression} :
    e ∈ es → Stuck td env e → Stuck td env (.tupleNew es)
  /-- Reading an element is stuck in its operand, on an operand that is not a tuple, or on a tuple
with nothing at the index.  The index is read off the expression rather than evaluated, so the last
is a fact about the value's length alone. -/
  | tupleGetOperand : Stuck td env e → Stuck td env (.tupleGet e i)
  | tupleGetNotTuple : Eval td env e v → ¬v.IsTuple → Stuck td env (.tupleGet e i)
  | tupleGetIndex : Eval td env e (.tuple vs) → vs[i]? = none → Stuck td env (.tupleGet e i)

/-- An `unreachable` is not stuck, and the omission is deliberate.

`Eval` has no rule for the form, so an expression reaching one has no value — but that is what the
form is *for*: reaching it is something a proof rules out, where everything this relation describes
is something the type checker was supposed to have ruled out already.  Progress would be false of a
relation that included it, and would say nothing about typing.

So `¬∃ v, Eval td env e v` has three sources and this relation covers one of them: going wrong,
divergence, and an `unreachable` reached. -/
public theorem Stuck.not_unreachable {td : TypeDecls} {env : Env} {t : Ty} {why : String} :
    ¬Stuck td env (.unreachable t why) := by
  rintro h
  cases h

/-- The element a stuck search reached is one a successful search already answered for, or the match
it stopped at.

`Stuck`'s three `listFindIndex` rules reach their element only once every element before it answered
`false`, and `EListFindIndexSome` says the same of its own prefix and match.  Two such
decompositions of one list therefore either agree on where the match is, or the successful search's
match sits inside the stuck one's prefix — and that is the case `Eval.unique` rules out, since that
element would have to answer both `true` and `false`. -/
private theorem Stuck.mem_pre_or_eq_of_findIndex {td : TypeDecls} {cenv : Env} {ps : Context}
    {body : Expression} {pre post pre' post' : List Value} {w w' : Value}
    (hlists : pre ++ w :: post = pre' ++ w' :: post')
    (hpre' : ∀ u ∈ pre', Eval td (Env.extend cenv ps [u]) body (.bool false))
    (hw : Eval td (Env.extend cenv ps [w]) body (.bool true)) : w' ∈ pre ∨ w' = w := by
  rcases Nat.lt_trichotomy pre'.length pre.length with hlt | heq | hgt
  · exact .inl (List.mem_of_append_cons_eq hlists.symm hlt)
  · obtain ⟨-, hcons⟩ := List.append_inj hlists heq.symm
    exact .inr (List.cons.inj hcons).1.symm
  · exact absurd (Eval.unique hw (hpre' _ (List.mem_of_append_cons_eq hlists hgt))) (by simp)

/-- Having a value excludes being stuck: an expression that evaluates to something does not reach a
form no rule of `Eval` can fire on.

This is the theorem that makes a progress proof about one declaration a *corollary* of the proof
that the declaration returns something, rather than the same induction written a second time for
failure.  A theorem of the shape `∃ v, d.Apply ... v` now gives `¬Stuck td (d.callEnv ...) d.body`
for nothing, and it needs no more hypotheses than the construction proof did — see
`CommentThread.linearize.not_stuck_body`, which is one line over
`CommentThread.linearize.apply_exists`.

The proof is an induction on the `Eval` derivation, and the two kinds of rule `Stuck` has are
refuted two different ways:

* a *propagation* rule speaks of a subexpression that must be evaluated, so there is a
  subderivation, and the induction hypothesis is exactly its refutation.  Where `Eval`'s premise
  runs over a `List.zip` — one evaluation per element — the induction hypothesis does too, and
  `List.exists_mem_zip_left` is what reads it back at the one element `Stuck` names.  Where it runs
  over a prefix, as `EListFindIndexSome`'s does, the induction hypothesis is prefixed the same way,
  which is exactly what `Stuck.listFindIndexCall` asks for.
* a *mismatch* rule carries an `Eval` premise of its own for the value it then objects to, and
  `Eval.unique` identifies that value with the one the derivation at hand produced.  That is the
  whole of what determinism buys here, and it is why these cases are one line apiece.

The `listFindIndex` rules are the one place more is needed: the element `Stuck` names is reached
only when every element before it answered `false`, so it either falls inside the prefix this
derivation already answered for or it is the match itself — `Stuck.mem_pre_or_eq_of_findIndex` is
that case split, and the remaining case is a derivation that reached *past* the match, which
`Eval.unique` refutes. -/
public theorem Eval.not_stuck {td : TypeDecls} {env : Env} {e : Expression} {v : Value}
    (h : Eval td env e v) : ¬Stuck td env e := by
  induction h with
  | ELam ps body => rintro hs; cases hs
  | EApp f args hf hlen hargs hat hbody ihf ihargs ihbody =>
    rintro hs
    cases hs with
    | appFn h => exact ihf h
    | appFnNotClosure hev hn => obtain rfl := Eval.unique hf hev; exact hn ⟨_, _, _, _, rfl⟩
    | appArg hmem h =>
      obtain ⟨_, hb⟩ := List.exists_mem_zip_left hlen hmem
      exact ihargs _ hb h
    | appArgs hev hlen' hargs' hnat =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (Eval.unique hf hev)
      obtain rfl := List.eq_of_zip_unique hlen' hlen
        fun p hp q hq hpq => Eval.unique (hargs' p hp) (by rw [hpq]; exact hargs q hq)
      exact hnat hat
    | appBody hev hlen' hargs' _ h =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (Eval.unique hf hev)
      obtain rfl := List.eq_of_zip_unique hlen' hlen
        fun p hp q hq hpq => Eval.unique (hargs' p hp) (by rw [hpq]; exact hargs q hq)
      exact ihbody h
  | EBoolLit b => rintro hs; cases hs
  | EIteTrue c thn els hc hthn ihc ihthn =>
    rintro hs
    cases hs with
    | iteCond h => exact ihc h
    | iteNotBool hev hn => obtain rfl := Eval.unique hc hev; exact hn ⟨_, rfl⟩
    | iteThen _ h => exact ihthn h
    | iteElse hev _ => exact absurd (Eval.unique hc hev) (by simp)
  | EIteFalse c thn els hc hels ihc ihels =>
    rintro hs
    cases hs with
    | iteCond h => exact ihc h
    | iteNotBool hev hn => obtain rfl := Eval.unique hc hev; exact hn ⟨_, rfl⟩
    | iteThen hev _ => exact absurd (Eval.unique hc hev) (by simp)
    | iteElse _ h => exact ihels h
  | EBoolAndFalse l r hl ihl =>
    rintro hs
    cases hs with
    | boolAndLeft h => exact ihl h
    | boolAndLeftNotBool hev hn => obtain rfl := Eval.unique hl hev; exact hn ⟨_, rfl⟩
    | boolAndRight hev _ => exact absurd (Eval.unique hl hev) (by simp)
    | boolAndRightNotBool hev _ _ => exact absurd (Eval.unique hl hev) (by simp)
  | EBoolAndTrue l r hl hr ihl ihr =>
    rintro hs
    cases hs with
    | boolAndLeft h => exact ihl h
    | boolAndLeftNotBool hev hn => obtain rfl := Eval.unique hl hev; exact hn ⟨_, rfl⟩
    | boolAndRight _ h => exact ihr h
    | boolAndRightNotBool _ hev hn => obtain rfl := Eval.unique hr hev; exact hn ⟨_, rfl⟩
  | EBoolOrTrue l r hl ihl =>
    rintro hs
    cases hs with
    | boolOrLeft h => exact ihl h
    | boolOrLeftNotBool hev hn => obtain rfl := Eval.unique hl hev; exact hn ⟨_, rfl⟩
    | boolOrRight hev _ => exact absurd (Eval.unique hl hev) (by simp)
    | boolOrRightNotBool hev _ _ => exact absurd (Eval.unique hl hev) (by simp)
  | EBoolOrFalse l r hl hr ihl ihr =>
    rintro hs
    cases hs with
    | boolOrLeft h => exact ihl h
    | boolOrLeftNotBool hev hn => obtain rfl := Eval.unique hl hev; exact hn ⟨_, rfl⟩
    | boolOrRight _ h => exact ihr h
    | boolOrRightNotBool _ hev hn => obtain rfl := Eval.unique hr hev; exact hn ⟨_, rfl⟩
  | EEquals l r hl hr hbeq ihl ihr =>
    rintro hs
    cases hs with
    | equalsLeft h => exact ihl h
    | equalsRight h => exact ihr h
    | equalsIncomparable hev₁ hev₂ hnone =>
      obtain rfl := Eval.unique hl hev₁
      obtain rfl := Eval.unique hr hev₂
      simp [hbeq] at hnone
  | ELt l r hl hr hlt ihl ihr =>
    rintro hs
    cases hs with
    | ltLeft h => exact ihl h
    | ltRight h => exact ihr h
    | ltIncomparable hev₁ hev₂ hnone =>
      obtain rfl := Eval.unique hl hev₁
      obtain rfl := Eval.unique hr hev₂
      simp [hlt] at hnone
  | ELe l r hl hr hle ihl ihr =>
    rintro hs
    cases hs with
    | leLeft h => exact ihl h
    | leRight h => exact ihr h
    | leIncomparable hev₁ hev₂ hnone =>
      obtain rfl := Eval.unique hl hev₁
      obtain rfl := Eval.unique hr hev₂
      simp [hle] at hnone
  | ELet x e body he hbody ihe ihbody =>
    rintro hs
    cases hs with
    | letBound h => exact ihe h
    | letBody hev h => obtain rfl := Eval.unique he hev; exact ihbody h
  | EVarRef x hx =>
    rintro hs
    cases hs with
    | varRefUnbound hnone => simp [hx] at hnone
  | EStructNew name fes hnames hev ihev =>
    rintro hs
    cases hs with
    | structNewField hmem h =>
      obtain ⟨_, hb⟩ :=
        List.exists_mem_zip_left (by simpa using congrArg List.length hnames) hmem
      exact ihev _ hb h
  | EStructGet e f he hf ihe =>
    rintro hs
    cases hs with
    | structGetOperand h => exact ihe h
    | structGetNotStruct hev hn => obtain rfl := Eval.unique he hev; exact hn ⟨_, _, rfl⟩
    | structGetMissing hev hnone =>
      obtain ⟨rfl, rfl⟩ := Value.struct.inj (Eval.unique he hev)
      simp [hf] at hnone
  | EStructUpdate e fes he hnames hev ihe ihev =>
    rintro hs
    cases hs with
    | structUpdateOperand h => exact ihe h
    | structUpdateNotStruct hev' hn => obtain rfl := Eval.unique he hev'; exact hn ⟨_, _, rfl⟩
    | structUpdateField hmem h =>
      obtain ⟨_, hb⟩ :=
        List.exists_mem_zip_left (by simpa using congrArg List.length hnames) hmem
      exact ihev _ hb h
  | EIndNew name c args hlen hev ihev =>
    rintro hs
    cases hs with
    | indNewArg hmem h =>
      obtain ⟨_, hb⟩ := List.exists_mem_zip_left hlen hmem
      exact ihev _ hb h
  | EIndMatch scrut alts hscrut hlookup hbody ihscrut ihbody =>
    rintro hs
    cases hs with
    | indMatchScrut h => exact ihscrut h
    | indMatchNotInd hev hn => obtain rfl := Eval.unique hscrut hev; exact hn ⟨_, _, _, rfl⟩
    | indMatchNoAlt hev hnone =>
      obtain ⟨rfl, rfl, rfl⟩ := Value.ind.inj (Eval.unique hscrut hev)
      simp [hlookup] at hnone
    | indMatchBody hev hlookup' h =>
      obtain ⟨rfl, rfl, rfl⟩ := Value.ind.inj (Eval.unique hscrut hev)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hlookup.symm.trans hlookup'))
      exact ihbody h
  | EIntLit i => rintro hs; cases hs
  | EPlus e₁ e₂ h₁ h₂ ih₁ ih₂ =>
    rintro hs
    cases hs with
    | plusLeft h => exact ih₁ h
    | plusLeftNotInt hev hn => obtain rfl := Eval.unique h₁ hev; exact hn ⟨_, rfl⟩
    | plusRight h => exact ih₂ h
    | plusRightNotInt hev hn => obtain rfl := Eval.unique h₂ hev; exact hn ⟨_, rfl⟩
  | EMinus e₁ e₂ h₁ h₂ ih₁ ih₂ =>
    rintro hs
    cases hs with
    | minusLeft h => exact ih₁ h
    | minusLeftNotInt hev hn => obtain rfl := Eval.unique h₁ hev; exact hn ⟨_, rfl⟩
    | minusRight h => exact ih₂ h
    | minusRightNotInt hev hn => obtain rfl := Eval.unique h₂ hev; exact hn ⟨_, rfl⟩
  | EMin e₁ e₂ h₁ h₂ ih₁ ih₂ =>
    rintro hs
    cases hs with
    | minLeft h => exact ih₁ h
    | minLeftNotInt hev hn => obtain rfl := Eval.unique h₁ hev; exact hn ⟨_, rfl⟩
    | minRight h => exact ih₂ h
    | minRightNotInt hev hn => obtain rfl := Eval.unique h₂ hev; exact hn ⟨_, rfl⟩
  | EMax e₁ e₂ h₁ h₂ ih₁ ih₂ =>
    rintro hs
    cases hs with
    | maxLeft h => exact ih₁ h
    | maxLeftNotInt hev hn => obtain rfl := Eval.unique h₁ hev; exact hn ⟨_, rfl⟩
    | maxRight h => exact ih₂ h
    | maxRightNotInt hev hn => obtain rfl := Eval.unique h₂ hev; exact hn ⟨_, rfl⟩
  | EStringLit s => rintro hs; cases hs
  | ENone ty => rintro hs; cases hs
  | ESome e he ihe =>
    rintro hs
    cases hs with
    | optionSomeInner h => exact ihe h
  | EOptionMatchNone scrut nbody x sbody hscrut hnbody ihscrut ihnbody =>
    rintro hs
    cases hs with
    | optionMatchScrut h => exact ihscrut h
    | optionMatchNotOption hev hn => obtain rfl := Eval.unique hscrut hev; exact hn ⟨_, rfl⟩
    | optionMatchNone _ h => exact ihnbody h
    | optionMatchSome hev _ => exact absurd (Eval.unique hscrut hev) (by simp)
  | EOptionMatchSome scrut nbody x sbody hscrut hsbody ihscrut ihsbody =>
    rintro hs
    cases hs with
    | optionMatchScrut h => exact ihscrut h
    | optionMatchNotOption hev hn => obtain rfl := Eval.unique hscrut hev; exact hn ⟨_, rfl⟩
    | optionMatchNone hev _ => exact absurd (Eval.unique hscrut hev) (by simp)
    | optionMatchSome hev h =>
      obtain rfl := Option.some.inj (Value.option.inj (Eval.unique hscrut hev))
      exact ihsbody h
  | ENil ty => rintro hs; cases hs
  | ECons e₁ e₂ h₁ h₂ ih₁ ih₂ =>
    rintro hs
    cases hs with
    | lconsHead h => exact ih₁ h
    | lconsTail h => exact ih₂ h
    | lconsTailNotList hev hn => obtain rfl := Eval.unique h₂ hev; exact hn ⟨_, rfl⟩
  | EListMatchNil scrut nbody hd tl cbody hscrut hnbody ihscrut ihnbody =>
    rintro hs
    cases hs with
    | listMatchScrut h => exact ihscrut h
    | listMatchNotList hev hn => obtain rfl := Eval.unique hscrut hev; exact hn ⟨_, rfl⟩
    | listMatchNil _ h => exact ihnbody h
    | listMatchCons hev _ => exact absurd (Eval.unique hscrut hev) (by simp)
  | EListMatchCons scrut nbody hd tl cbody hscrut hcbody ihscrut ihcbody =>
    rintro hs
    cases hs with
    | listMatchScrut h => exact ihscrut h
    | listMatchNotList hev hn => obtain rfl := Eval.unique hscrut hev; exact hn ⟨_, rfl⟩
    | listMatchNil hev _ => exact absurd (Eval.unique hscrut hev) (by simp)
    | listMatchCons hev h =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj (Value.list.inj (Eval.unique hscrut hev))
      exact ihcbody h
  | EListIndex l i hl hi ihl ihi =>
    rintro hs
    cases hs with
    | listIndexOperand h => exact ihl h
    | listIndexNotList hev hn => obtain rfl := Eval.unique hl hev; exact hn ⟨_, rfl⟩
    | listIndexIndex h => exact ihi h
    | listIndexIndexNotInt hev hn => obtain rfl := Eval.unique hi hev; exact hn ⟨_, rfl⟩
  | EListMap e f he hf hlen hat hev ihe ihf ihev =>
    rintro hs
    cases hs with
    | listMapOperand h => exact ihe h
    | listMapNotList hev' hn => obtain rfl := Eval.unique he hev'; exact hn ⟨_, rfl⟩
    | listMapFn h => exact ihf h
    | listMapFnNotClosure hev' hn =>
      obtain rfl := Eval.unique hf hev'; exact hn ⟨_, _, _, _, rfl⟩
    | listMapArg hel hfl hmem hnat =>
      obtain rfl := Value.list.inj (Eval.unique he hel)
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (Eval.unique hf hfl)
      obtain ⟨_, hb⟩ := List.exists_mem_zip_left hlen hmem
      exact hnat (hat _ hb)
    | listMapCall hel hfl hmem _ h =>
      obtain rfl := Value.list.inj (Eval.unique he hel)
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (Eval.unique hf hfl)
      obtain ⟨_, hb⟩ := List.exists_mem_zip_left hlen hmem
      exact ihev _ hb h
  | EListFlatMap e f he hf hlen hat hev ihe ihf ihev =>
    rintro hs
    cases hs with
    | listFlatMapOperand h => exact ihe h
    | listFlatMapNotList hev' hn => obtain rfl := Eval.unique he hev'; exact hn ⟨_, rfl⟩
    | listFlatMapFn h => exact ihf h
    | listFlatMapFnNotClosure hev' hn =>
      obtain rfl := Eval.unique hf hev'; exact hn ⟨_, _, _, _, rfl⟩
    | listFlatMapArg hel hfl hmem hnat =>
      obtain rfl := Value.list.inj (Eval.unique he hel)
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (Eval.unique hf hfl)
      obtain ⟨_, hb⟩ := List.exists_mem_zip_left hlen hmem
      exact hnat (hat _ hb)
    | listFlatMapCall hel hfl hmem _ h =>
      obtain rfl := Value.list.inj (Eval.unique he hel)
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (Eval.unique hf hfl)
      obtain ⟨_, hb⟩ := List.exists_mem_zip_left hlen hmem
      exact ihev _ hb h
    | listFlatMapCallNotList hel hfl hmem _ hev' hn =>
      obtain rfl := Value.list.inj (Eval.unique he hel)
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (Eval.unique hf hfl)
      obtain ⟨_, hb⟩ := List.exists_mem_zip_left hlen hmem
      obtain rfl := Eval.unique (hev _ hb) hev'
      exact hn ⟨_, rfl⟩
  | EListLength e he ihe =>
    rintro hs
    cases hs with
    | listLengthOperand h => exact ihe h
    | listLengthNotList hev hn => obtain rfl := Eval.unique he hev; exact hn ⟨_, rfl⟩
  | EListFindIndexSome e f he hf hatpre hpre hatw hw ihe ihf ihpre ihw =>
    rintro hs
    cases hs with
    | listFindIndexOperand h => exact ihe h
    | listFindIndexNotList hev hn => obtain rfl := Eval.unique he hev; exact hn ⟨_, rfl⟩
    | listFindIndexFn h => exact ihf h
    | listFindIndexFnNotClosure hev hn =>
      obtain rfl := Eval.unique hf hev; exact hn ⟨_, _, _, _, rfl⟩
    | listFindIndexArg hel hfl _ hpre' hnat =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (Eval.unique hf hfl)
      rcases Stuck.mem_pre_or_eq_of_findIndex (Value.list.inj (Eval.unique he hel)) hpre' hw with
        hmem | rfl
      · exact hnat (hatpre _ hmem)
      · exact hnat hatw
    | listFindIndexCall hel hfl _ hpre' _ h =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (Eval.unique hf hfl)
      rcases Stuck.mem_pre_or_eq_of_findIndex (Value.list.inj (Eval.unique he hel)) hpre' hw with
        hmem | rfl
      · exact ihpre _ hmem h
      · exact ihw h
    | listFindIndexCallNotBool hel hfl _ hpre' _ hev hn =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (Eval.unique hf hfl)
      rcases Stuck.mem_pre_or_eq_of_findIndex (Value.list.inj (Eval.unique he hel)) hpre' hw with
        hmem | rfl
      · obtain rfl := Eval.unique (hpre _ hmem) hev
        exact hn ⟨_, rfl⟩
      · obtain rfl := Eval.unique hw hev
        exact hn ⟨_, rfl⟩
  | EListFindIndexNone e f he hf hat hall ihe ihf ihall =>
    rintro hs
    cases hs with
    | listFindIndexOperand h => exact ihe h
    | listFindIndexNotList hev hn => obtain rfl := Eval.unique he hev; exact hn ⟨_, rfl⟩
    | listFindIndexFn h => exact ihf h
    | listFindIndexFnNotClosure hev hn =>
      obtain rfl := Eval.unique hf hev; exact hn ⟨_, _, _, _, rfl⟩
    | listFindIndexArg hel hfl _ _ hnat =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (Eval.unique hf hfl)
      obtain rfl := Value.list.inj (Eval.unique he hel)
      exact hnat (hat _ (by simp))
    | listFindIndexCall hel hfl _ _ _ h =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (Eval.unique hf hfl)
      obtain rfl := Value.list.inj (Eval.unique he hel)
      exact ihall _ (by simp) h
    | listFindIndexCallNotBool hel hfl _ _ _ hev hn =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (Eval.unique hf hfl)
      obtain rfl := Value.list.inj (Eval.unique he hel)
      obtain rfl := Eval.unique (hall _ (by simp)) hev
      exact hn ⟨_, rfl⟩
  | EListReverse e he ihe =>
    rintro hs
    cases hs with
    | listReverseOperand h => exact ihe h
    | listReverseNotList hev hn => obtain rfl := Eval.unique he hev; exact hn ⟨_, rfl⟩
  | EListSortOn e f he hf hlen hat hev hcmp ihe ihf ihev =>
    rintro hs
    cases hs with
    | listSortOnOperand h => exact ihe h
    | listSortOnNotList hev' hn => obtain rfl := Eval.unique he hev'; exact hn ⟨_, rfl⟩
    | listSortOnFn h => exact ihf h
    | listSortOnFnNotClosure hev' hn =>
      obtain rfl := Eval.unique hf hev'; exact hn ⟨_, _, _, _, rfl⟩
    | listSortOnArg hel hfl hmem hnat =>
      obtain rfl := Value.list.inj (Eval.unique he hel)
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (Eval.unique hf hfl)
      obtain ⟨_, hb⟩ := List.exists_mem_zip_left hlen hmem
      exact hnat (hat _ hb)
    | listSortOnCall hel hfl hmem _ h =>
      obtain rfl := Value.list.inj (Eval.unique he hel)
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (Eval.unique hf hfl)
      obtain ⟨_, hb⟩ := List.exists_mem_zip_left hlen hmem
      exact ihev _ hb h
    | listSortOnKeys hel hfl ha hb _ _ hka hkb hnone =>
      obtain rfl := Value.list.inj (Eval.unique he hel)
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (Eval.unique hf hfl)
      obtain ⟨_, hza⟩ := List.exists_mem_zip_left hlen ha
      obtain ⟨_, hzb⟩ := List.exists_mem_zip_left hlen hb
      obtain rfl := Eval.unique (hev _ hza) hka
      obtain rfl := Eval.unique (hev _ hzb) hkb
      have := hcmp _ (List.of_mem_zip hza).2 _ (List.of_mem_zip hzb).2
      simp [hnone] at this
  | EListSortBy e f he hf hat hev ihe ihf ihev =>
    rintro hs
    cases hs with
    | listSortByOperand h => exact ihe h
    | listSortByNotList hev' hn => obtain rfl := Eval.unique he hev'; exact hn ⟨_, rfl⟩
    | listSortByFn h => exact ihf h
    | listSortByFnNotClosure hev' hn =>
      obtain rfl := Eval.unique hf hev'; exact hn ⟨_, _, _, _, rfl⟩
    | listSortByArgs hel hfl ha hb hnat =>
      obtain rfl := Value.list.inj (Eval.unique he hel)
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (Eval.unique hf hfl)
      exact hnat (hat _ ha _ hb)
    | listSortByCall hel hfl ha hb _ h =>
      obtain rfl := Value.list.inj (Eval.unique he hel)
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (Eval.unique hf hfl)
      exact ihev _ ha _ hb h
    | listSortByCallNotBool hel hfl ha hb _ hev' hn =>
      obtain rfl := Value.list.inj (Eval.unique he hel)
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (Eval.unique hf hfl)
      obtain rfl := Eval.unique (hev _ ha _ hb) hev'
      exact hn ⟨_, rfl⟩
  | EHashmapEmpty kt vt => rintro hs; cases hs
  | EHashmapPut m k val hm hk hval herase ihm ihk ihval =>
    rintro hs
    cases hs with
    | hashmapPutMap h => exact ihm h
    | hashmapPutMapNotHashmap hev hn => obtain rfl := Eval.unique hm hev; exact hn ⟨_, rfl⟩
    | hashmapPutKey h => exact ihk h
    | hashmapPutValue h => exact ihval h
    | hashmapPutIncomparable hev hkev hnone =>
      obtain rfl := Value.hashmap.inj (Eval.unique hm hev)
      obtain rfl := Eval.unique hk hkev
      simp [herase] at hnone
  | EHashmapGet m k hm hk hlookup ihm ihk =>
    rintro hs
    cases hs with
    | hashmapGetMap h => exact ihm h
    | hashmapGetMapNotHashmap hev hn => obtain rfl := Eval.unique hm hev; exact hn ⟨_, rfl⟩
    | hashmapGetKey h => exact ihk h
    | hashmapGetIncomparable hev hkev hnone =>
      obtain rfl := Value.hashmap.inj (Eval.unique hm hev)
      obtain rfl := Eval.unique hk hkev
      simp [hlookup] at hnone
  | EHashmapMap m f hm hf hkeys hat hev ihm ihf ihev =>
    rintro hs
    cases hs with
    | hashmapMapMap h => exact ihm h
    | hashmapMapMapNotHashmap hev' hn => obtain rfl := Eval.unique hm hev'; exact hn ⟨_, rfl⟩
    | hashmapMapFn h => exact ihf h
    | hashmapMapFnNotClosure hev' hn =>
      obtain rfl := Eval.unique hf hev'; exact hn ⟨_, _, _, _, rfl⟩
    | hashmapMapArgs hml hfl hmem hnat =>
      obtain rfl := Value.hashmap.inj (Eval.unique hm hml)
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (Eval.unique hf hfl)
      obtain ⟨_, hb⟩ :=
        List.exists_mem_zip_left (by simpa using congrArg List.length hkeys) hmem
      exact hnat (hat _ hb)
    | hashmapMapCall hml hfl hmem _ h =>
      obtain rfl := Value.hashmap.inj (Eval.unique hm hml)
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (Eval.unique hf hfl)
      obtain ⟨_, hb⟩ :=
        List.exists_mem_zip_left (by simpa using congrArg List.length hkeys) hmem
      exact ihev _ hb h
  | EHashmapToList m hm ihm =>
    rintro hs
    cases hs with
    | hashmapToListOperand h => exact ihm h
    | hashmapToListNotHashmap hev hn => obtain rfl := Eval.unique hm hev; exact hn ⟨_, rfl⟩
  | ETupleNew es hlen hev ihev =>
    rintro hs
    cases hs with
    | tupleNewElem hmem h =>
      obtain ⟨_, hb⟩ := List.exists_mem_zip_left hlen hmem
      exact ihev _ hb h
  | ETupleGet e i he hi ihe =>
    rintro hs
    cases hs with
    | tupleGetOperand h => exact ihe h
    | tupleGetNotTuple hev hn => obtain rfl := Eval.unique he hev; exact hn ⟨_, rfl⟩
    | tupleGetIndex hev hnone =>
      obtain rfl := Value.tuple.inj (Eval.unique he hev)
      simp [hi] at hnone

/-! ## Refuting a derivation, form by form

`¬Stuck` read along a body is what a progress proof about one declaration does, and it is the same
work at every form: take the relation apart, and refute each of that form's rules in turn.  A
propagation rule is refuted by `¬Stuck` of the subexpression it propagates from, and a mismatch rule
by *reading* the value a subexpression produced — every one of them carries an `Eval` premise, which
is why the lemmas below ask for hypotheses about what the subexpressions can evaluate to rather than
for evaluations of them.

Those hypotheses are stated over *every* value a subexpression can produce, not over one.  That is
what a mismatch rule hands over — the `Eval` premise it carries is a derivation of its own — and
when these were written nothing said it produced the same value as the caller's, so a lemma handed
a single evaluation would have had nothing to say to those rules.

`Eval.unique` now says it does, and the quantifier is no longer a cost to a caller that has an
evaluation in hand: `Eval.Yields.forall_eval` (Eval/Yields.lean) discharges one of these hypotheses
at the single value, which is what every `∀ v, Eval td env e v → P v` below amounts to now.  Where
a subexpression is determined — a `varRef`, a `lam` — it never was a cost: `Eval.varRef_inv` and
`Eval.lam_inv` answer for every value.

A form whose calls are the thing that can go wrong gets one hypothesis per element or pair rather
than one over the list, matching the rules: `Eval`'s premises run over a zip because a mapping
evaluates every call, where `Stuck` names the one element whose call went wrong.  The
`ArgsHaveType` clause and the `¬Stuck` clause are bundled into that one hypothesis, since a caller
proves both from the same facts about the element.

One lemma per form the model's bodies use, each asking for the premises of its own rules and
nothing else. -/

public theorem Stuck.not_varRef {td : TypeDecls} {env : Env} {x : String} {v : Value}
    (h : env.lookup x = some v) : ¬Stuck td env (.varRef x) := by
  rintro hs
  cases hs with
  | varRefUnbound hnone => simp [h] at hnone

public theorem Stuck.not_lam {td : TypeDecls} {env : Env} {ps : List (String × Ty)}
    {body : Expression} : ¬Stuck td env (.lam ps body) := by
  rintro hs
  cases hs

public theorem Stuck.not_intLit {td : TypeDecls} {env : Env} {i : Int} :
    ¬Stuck td env (.intLit i) := by
  rintro hs
  cases hs

/-- A `let` is not stuck where what it binds is not stuck and its body is not stuck under any
binding that expression can produce.  The two rules of `Stuck` it has, one apiece. -/
public theorem Stuck.not_let {td : TypeDecls} {env : Env} {x : String} {e body : Expression}
    (he : ¬Stuck td env e)
    (hbody : ∀ v, Eval td env e v → ¬Stuck td ⟨(x, v) :: env.bindings, env.globals⟩ body) :
    ¬Stuck td env (.let_ x e body) := by
  rintro hs
  cases hs with
  | letBound h => exact he h
  | letBody hev h => exact hbody _ hev h

/-- Reading a field is not stuck where its operand is not stuck and every value that operand can
produce carries the field.  One hypothesis refutes both mismatch rules: a value `Value.field?`
answers for is a struct value, and the answer is what `structGetMissing` says there is none of. -/
public theorem Stuck.not_structGet {td : TypeDecls} {env : Env} {e : Expression} {f : FieldName}
    (he : ¬Stuck td env e) (hf : ∀ v, Eval td env e v → ∃ w, v.field? f = some w) :
    ¬Stuck td env (.structGet e f) := by
  rintro hs
  cases hs with
  | structGetOperand h => exact he h
  | structGetNotStruct hev hns =>
    obtain ⟨w, hw⟩ := hf _ hev
    exact hns (Value.isStruct_of_field? hw)
  | structGetMissing hev hnone =>
    obtain ⟨w, hw⟩ := hf _ hev
    simp only [Value.field?] at hw
    simp [hw] at hnone

/-- The same at an operand that is a name the environment binds, which is where most field reads in
a body are: the operand is determined, so what it produces is that value and the field hypothesis
collapses to one read. -/
public theorem Stuck.not_structGet_varRef {td : TypeDecls} {env : Env} {x : String}
    {v : Value} {f : FieldName} {w : Value}
    (hx : env.lookup x = some v) (hf : v.field? f = some w) :
    ¬Stuck td env (.structGet (.varRef x) f) :=
  Stuck.not_structGet (Stuck.not_varRef hx) fun u hu => by
    rw [Option.some.inj ((Eval.varRef_inv hu).symm.trans hx)]
    exact ⟨w, hf⟩

/-- Building a struct is not stuck where none of its fields is: it has the one rule, and no mismatch
rule for a caller to refute. -/
public theorem Stuck.not_structNew {td : TypeDecls} {env : Env} {name : String}
    {fes : List (FieldName × Expression)} (hfes : ∀ p ∈ fes, ¬Stuck td env p.2) :
    ¬Stuck td env (.structNew name fes) := by
  rintro hs
  cases hs with
  | structNewField hmem h => exact hfes _ hmem h

/-- A call to a name the environment binds to a closure is not stuck where no argument is stuck, the
values the arguments can produce fit the closure's parameters, and the body is not stuck under them.

The closure is given by the binding rather than existential, which is what lets the last two
hypotheses speak of *this* closure's parameters and body: a `varRef` is determined, so the closure
`appArgs` and `appBody` entered is the one the environment holds.  It is given as an `Env.closure`
rather than as a `Value.closure` of two halves, because that is the form a `lam` evaluates to
(`Eval.lam_inv`) and the form `Globals.value` builds — and it is what makes the body's environment
an `Env.extend` of the environment the closure captured. -/
public theorem Stuck.not_app_varRef {td : TypeDecls} {env cenv : Env} {x : String} {ps : Context}
    {fbody : Expression} {args : List Expression}
    (hx : env.lookup x = some (cenv.closure ps fbody))
    (hargs : ∀ a ∈ args, ¬Stuck td env a)
    (hat : ∀ vs, args.length = vs.length → (∀ p ∈ args.zip vs, Eval td env p.1 p.2) →
      ArgsHaveType td ps vs)
    (hbody : ∀ vs, args.length = vs.length → (∀ p ∈ args.zip vs, Eval td env p.1 p.2) →
      ¬Stuck td (Env.extend cenv ps vs) fbody) :
    ¬Stuck td env (.app (.varRef x) args) := by
  rintro hs
  cases hs with
  | appFn h => exact Stuck.not_varRef hx h
  | appFnNotClosure hev hnc =>
    obtain rfl := Option.some.inj ((Eval.varRef_inv hev).symm.trans hx)
    exact hnc ⟨_, _, _, _, rfl⟩
  | appArgs hev hlen hvs hnat =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ ∧ _ := by
      simpa [Env.closure, Value.closure.injEq] using
        Option.some.inj ((Eval.varRef_inv hev).symm.trans hx)
    exact hnat (hat _ hlen hvs)
  | appArg hmem h => exact hargs _ hmem h
  | appBody hev hlen hvs _ h =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ ∧ _ := by
      simpa [Env.closure, Value.closure.injEq] using
        Option.some.inj ((Eval.varRef_inv hev).symm.trans hx)
    exact hbody _ hlen hvs h

/-- And a call to a name the *globals* declare, which is how a body calls another declaration.

`Stuck.not_app_varRef` at the closure `Env.lookup` builds out of the table, so that the body's
environment is the one a call really evaluates it in — `FuncDecl.callEnv`, which is what every
theorem about a declaration is stated over.  The two hypotheses are what `Env.lookup` consults, in
the order it consults them, exactly as in `FuncDecl.apply_of_eval_app`. -/
public theorem Stuck.not_app_global {td : TypeDecls} {env : Env} {x : String} {d : FuncDecl}
    {args : List Expression} (hd : env.globals.lookup x = some d)
    (hb : env.bindings.lookup x = none)
    (hargs : ∀ a ∈ args, ¬Stuck td env a)
    (hat : ∀ vs, args.length = vs.length → (∀ p ∈ args.zip vs, Eval td env p.1 p.2) →
      ArgsHaveType td d.parameters vs)
    (hbody : ∀ vs, args.length = vs.length → (∀ p ∈ args.zip vs, Eval td env p.1 p.2) →
      ¬Stuck td (d.callEnv env.globals vs) d.body) :
    ¬Stuck td env (.app (.varRef x) args) :=
  Stuck.not_app_varRef (cenv := Globals.env env.globals) (ps := d.parameters) (fbody := d.body)
    (by rw [Env.lookup_of_globals hb, hd, Option.map_some]; rfl) hargs hat hbody

/-- A comparison is not stuck where neither operand is and every pair of values they can produce has
an answer.  `Ty.comparable` is the type checker's side of that third hypothesis; nothing here
derives one from the other, so a caller supplies it about the values it has. -/
public theorem Stuck.not_equals {td : TypeDecls} {env : Env} {l r : Expression}
    (hl : ¬Stuck td env l) (hr : ¬Stuck td env r)
    (hcmp : ∀ v₁ v₂, Eval td env l v₁ → Eval td env r v₂ → (Value.beq? v₁ v₂).isSome) :
    ¬Stuck td env (.equals l r) := by
  rintro hs
  cases hs with
  | equalsLeft h => exact hl h
  | equalsRight h => exact hr h
  | equalsIncomparable h₁ h₂ hnone =>
    have := hcmp _ _ h₁ h₂
    simp [hnone] at this

/-- An ordering is the same three rules with `Value.le?` in place of `Value.beq?`. -/
public theorem Stuck.not_le {td : TypeDecls} {env : Env} {l r : Expression}
    (hl : ¬Stuck td env l) (hr : ¬Stuck td env r)
    (hcmp : ∀ v₁ v₂, Eval td env l v₁ → Eval td env r v₂ → (Value.le? v₁ v₂).isSome) :
    ¬Stuck td env (.le l r) := by
  rintro hs
  cases hs with
  | leLeft h => exact hl h
  | leRight h => exact hr h
  | leIncomparable h₁ h₂ hnone =>
    have := hcmp _ _ h₁ h₂
    simp [hnone] at this

/-- Arithmetic is not stuck where neither operand is and both produce `int`s.  Four rules, two per
operand, because both operands are always evaluated. -/
public theorem Stuck.not_plus {td : TypeDecls} {env : Env} {e₁ e₂ : Expression}
    (h₁ : ¬Stuck td env e₁) (h₂ : ¬Stuck td env e₂)
    (hi₁ : ∀ v, Eval td env e₁ v → v.IsInt) (hi₂ : ∀ v, Eval td env e₂ v → v.IsInt) :
    ¬Stuck td env (.plus e₁ e₂) := by
  rintro hs
  cases hs with
  | plusLeft h => exact h₁ h
  | plusLeftNotInt hev hn => exact hn (hi₁ _ hev)
  | plusRight h => exact h₂ h
  | plusRightNotInt hev hn => exact hn (hi₂ _ hev)

public theorem Stuck.not_minus {td : TypeDecls} {env : Env} {e₁ e₂ : Expression}
    (h₁ : ¬Stuck td env e₁) (h₂ : ¬Stuck td env e₂)
    (hi₁ : ∀ v, Eval td env e₁ v → v.IsInt) (hi₂ : ∀ v, Eval td env e₂ v → v.IsInt) :
    ¬Stuck td env (.minus e₁ e₂) := by
  rintro hs
  cases hs with
  | minusLeft h => exact h₁ h
  | minusLeftNotInt hev hn => exact hn (hi₁ _ hev)
  | minusRight h => exact h₂ h
  | minusRightNotInt hev hn => exact hn (hi₂ _ hev)

public theorem Stuck.not_min {td : TypeDecls} {env : Env} {e₁ e₂ : Expression}
    (h₁ : ¬Stuck td env e₁) (h₂ : ¬Stuck td env e₂)
    (hi₁ : ∀ v, Eval td env e₁ v → v.IsInt) (hi₂ : ∀ v, Eval td env e₂ v → v.IsInt) :
    ¬Stuck td env (.min e₁ e₂) := by
  rintro hs
  cases hs with
  | minLeft h => exact h₁ h
  | minLeftNotInt hev hn => exact hn (hi₁ _ hev)
  | minRight h => exact h₂ h
  | minRightNotInt hev hn => exact hn (hi₂ _ hev)

/-- A match on an option whose empty case is an `unreachable` is not stuck where its scrutinee is not
stuck, produces options, and leaves the other case not stuck under whatever it bound.

The empty case needs nothing: `Stuck.not_unreachable` refutes `optionMatchNone` whatever the
scrutinee did, which is the same omission `Eval.optionMatch_unreachable_inv` reads the other way. -/
public theorem Stuck.not_optionMatch_unreachable {td : TypeDecls} {env : Env} {scrut : Expression}
    {t : Ty} {why x : String} {sbody : Expression} (hscrut : ¬Stuck td env scrut)
    (hopt : ∀ v, Eval td env scrut v → v.IsOption)
    (hbody : ∀ w, Eval td env scrut (.option (some w)) →
      ¬Stuck td ⟨(x, w) :: env.bindings, env.globals⟩ sbody) :
    ¬Stuck td env (.optionMatch scrut (.unreachable t why) x sbody) := by
  rintro hs
  cases hs with
  | optionMatchScrut h => exact hscrut h
  | optionMatchNotOption hev hn => exact hn (hopt _ hev)
  | optionMatchNone _ h => exact Stuck.not_unreachable h
  | optionMatchSome hev h => exact hbody _ hev h

/-- A cons is not stuck where neither operand is and the tail produces lists.  Nothing is asked of
the head: a list's element type is whatever the head turned out to be. -/
public theorem Stuck.not_lcons {td : TypeDecls} {env : Env} {e₁ e₂ : Expression}
    (h₁ : ¬Stuck td env e₁) (h₂ : ¬Stuck td env e₂)
    (hl : ∀ v, Eval td env e₂ v → v.IsList) : ¬Stuck td env (.lcons e₁ e₂) := by
  rintro hs
  cases hs with
  | lconsHead h => exact h₁ h
  | lconsTail h => exact h₂ h
  | lconsTailNotList hev hn => exact hn (hl _ hev)

/-- A length is not stuck where its operand is not stuck and produces lists, and that is all either
of its two rules can be. -/
public theorem Stuck.not_listLength {td : TypeDecls} {env : Env} {e : Expression}
    (he : ¬Stuck td env e) (hl : ∀ v, Eval td env e v → v.IsList) :
    ¬Stuck td env (.listLength e) := by
  rintro hs
  cases hs with
  | listLengthOperand h => exact he h
  | listLengthNotList hev hn => exact hn (hl _ hev)

/-- An index is not stuck where neither operand is, the first produces lists and the second `int`s.
An index the list has no element at is not among its rules — that is the empty option, which is a
value like any other — so nothing is asked about the position. -/
public theorem Stuck.not_listIndex {td : TypeDecls} {env : Env} {l i : Expression}
    (hl : ¬Stuck td env l) (hi : ¬Stuck td env i)
    (hlist : ∀ v, Eval td env l v → v.IsList) (hint : ∀ v, Eval td env i v → v.IsInt) :
    ¬Stuck td env (.listIndex l i) := by
  rintro hs
  cases hs with
  | listIndexOperand h => exact hl h
  | listIndexNotList hev hn => exact hn (hlist _ hev)
  | listIndexIndex h => exact hi h
  | listIndexIndexNotInt hev hn => exact hn (hint _ hev)

/-- A get on a hashmap is not stuck where neither operand is, the first produces hashmaps, and every
key the second can produce has an answer in them.  A key the map does not bind is not among its
rules: that is the empty option, so what the last hypothesis rules out is a key that cannot be
*compared*. -/
public theorem Stuck.not_hashmapGet {td : TypeDecls} {env : Env} {m k : Expression}
    (hm : ¬Stuck td env m) (hk : ¬Stuck td env k)
    (hmap : ∀ v, Eval td env m v → v.IsHashmap)
    (hlookup : ∀ kvs vk, Eval td env m (.hashmap kvs) → Eval td env k vk →
      (KeyValues.lookup? kvs vk).isSome) :
    ¬Stuck td env (.hashmapGet m k) := by
  rintro hs
  cases hs with
  | hashmapGetMap h => exact hm h
  | hashmapGetMapNotHashmap hev hn => exact hn (hmap _ hev)
  | hashmapGetKey h => exact hk h
  | hashmapGetIncomparable hev hkev hnone =>
    have := hlookup _ _ hev hkev
    simp [hnone] at this

/-- A mapping is not stuck where neither operand is, the first produces lists, the second closures,
and every call it makes fits the closure and is not stuck.

`hcall` is the one hypothesis the last two rules share, and it is stated per element: a mapping is
stuck as soon as one call is, so which element that was is the whole of what those rules say. -/
public theorem Stuck.not_listMap {td : TypeDecls} {env : Env} {e f : Expression}
    (he : ¬Stuck td env e) (hf : ¬Stuck td env f)
    (hlist : ∀ v, Eval td env e v → v.IsList)
    (hclosure : ∀ v, Eval td env f v → v.IsClosure)
    (hcall : ∀ (vs : List Value) (cb : Bindings) (cg : Globals) (ps : Context) (body : Expression),
      Eval td env e (.list vs) → Eval td env f (.closure cb cg ps body) → ∀ w ∈ vs,
        ArgsHaveType td ps [w] ∧ ¬Stuck td (Env.extend ⟨cb, cg⟩ ps [w]) body) :
    ¬Stuck td env (.listMap e f) := by
  rintro hs
  cases hs with
  | listMapOperand h => exact he h
  | listMapNotList hev hn => exact hn (hlist _ hev)
  | listMapFn h => exact hf h
  | listMapFnNotClosure hev hn => exact hn (hclosure _ hev)
  | listMapArg hel hfl hmem hnat => exact hnat (hcall _ _ _ _ _ hel hfl _ hmem).1
  | listMapCall hel hfl hmem _ h => exact (hcall _ _ _ _ _ hel hfl _ hmem).2 h

/-- A flat mapping is a mapping's hypotheses with one more clause on each call: what it produced is
a list, which is the one thing this form asks of a call's result. -/
public theorem Stuck.not_listFlatMap {td : TypeDecls} {env : Env} {e f : Expression}
    (he : ¬Stuck td env e) (hf : ¬Stuck td env f)
    (hlist : ∀ v, Eval td env e v → v.IsList)
    (hclosure : ∀ v, Eval td env f v → v.IsClosure)
    (hcall : ∀ (vs : List Value) (cb : Bindings) (cg : Globals) (ps : Context) (body : Expression),
      Eval td env e (.list vs) → Eval td env f (.closure cb cg ps body) → ∀ w ∈ vs,
        ArgsHaveType td ps [w] ∧ ¬Stuck td (Env.extend ⟨cb, cg⟩ ps [w]) body ∧
          ∀ u, Eval td (Env.extend ⟨cb, cg⟩ ps [w]) body u → u.IsList) :
    ¬Stuck td env (.listFlatMap e f) := by
  rintro hs
  cases hs with
  | listFlatMapOperand h => exact he h
  | listFlatMapNotList hev hn => exact hn (hlist _ hev)
  | listFlatMapFn h => exact hf h
  | listFlatMapFnNotClosure hev hn => exact hn (hclosure _ hev)
  | listFlatMapArg hel hfl hmem hnat => exact hnat (hcall _ _ _ _ _ hel hfl _ hmem).1
  | listFlatMapCall hel hfl hmem _ h => exact (hcall _ _ _ _ _ hel hfl _ hmem).2.1 h
  | listFlatMapCallNotList hel hfl hmem _ hev hn =>
    exact hn ((hcall _ _ _ _ _ hel hfl _ hmem).2.2 _ hev)

/-- A search is a flat mapping's hypotheses with a `bool` asked of each call in place of a list, and
with the calls spoken for over the whole list rather than over the elements the search reaches.

That is weaker than the rules allow — an element after the first match is never handed to the
predicate — and it is what a caller can supply: which elements were reached depends on what the
calls answered, so a hypothesis about all of them is the one that does not have to know. -/
public theorem Stuck.not_listFindIndex {td : TypeDecls} {env : Env} {e f : Expression}
    (he : ¬Stuck td env e) (hf : ¬Stuck td env f)
    (hlist : ∀ v, Eval td env e v → v.IsList)
    (hclosure : ∀ v, Eval td env f v → v.IsClosure)
    (hcall : ∀ (vs : List Value) (cb : Bindings) (cg : Globals) (ps : Context) (body : Expression),
      Eval td env e (.list vs) → Eval td env f (.closure cb cg ps body) → ∀ w ∈ vs,
        ArgsHaveType td ps [w] ∧ ¬Stuck td (Env.extend ⟨cb, cg⟩ ps [w]) body ∧
          ∀ u, Eval td (Env.extend ⟨cb, cg⟩ ps [w]) body u → u.IsBool) :
    ¬Stuck td env (.listFindIndex e f) := by
  rintro hs
  cases hs with
  | listFindIndexOperand h => exact he h
  | listFindIndexNotList hev hn => exact hn (hlist _ hev)
  | listFindIndexFn h => exact hf h
  | listFindIndexFnNotClosure hev hn => exact hn (hclosure _ hev)
  | listFindIndexArg hel hfl _ _ hnat =>
    exact hnat (hcall _ _ _ _ _ hel hfl _ (by simp)).1
  | listFindIndexCall hel hfl _ _ _ h =>
    exact (hcall _ _ _ _ _ hel hfl _ (by simp)).2.1 h
  | listFindIndexCallNotBool hel hfl _ _ _ hev hn =>
    exact hn ((hcall _ _ _ _ _ hel hfl _ (by simp)).2.2 _ hev)

/-- A sort by a comparison is a search's hypotheses with the calls taking two elements rather than
one: the comparison is asked about a pair, so `hcall` is over two elements of the list. -/
public theorem Stuck.not_listSortBy {td : TypeDecls} {env : Env} {e f : Expression}
    (he : ¬Stuck td env e) (hf : ¬Stuck td env f)
    (hlist : ∀ v, Eval td env e v → v.IsList)
    (hclosure : ∀ v, Eval td env f v → v.IsClosure)
    (hcall : ∀ (vs : List Value) (cb : Bindings) (cg : Globals) (ps : Context) (body : Expression),
      Eval td env e (.list vs) → Eval td env f (.closure cb cg ps body) → ∀ a ∈ vs, ∀ b ∈ vs,
        ArgsHaveType td ps [a, b] ∧ ¬Stuck td (Env.extend ⟨cb, cg⟩ ps [a, b]) body ∧
          ∀ u, Eval td (Env.extend ⟨cb, cg⟩ ps [a, b]) body u → u.IsBool) :
    ¬Stuck td env (.listSortBy e f) := by
  rintro hs
  cases hs with
  | listSortByOperand h => exact he h
  | listSortByNotList hev hn => exact hn (hlist _ hev)
  | listSortByFn h => exact hf h
  | listSortByFnNotClosure hev hn => exact hn (hclosure _ hev)
  | listSortByArgs hel hfl ha hb hnat => exact hnat (hcall _ _ _ _ _ hel hfl _ ha _ hb).1
  | listSortByCall hel hfl ha hb _ h => exact (hcall _ _ _ _ _ hel hfl _ ha _ hb).2.1 h
  | listSortByCallNotBool hel hfl ha hb _ hev hn =>
    exact hn ((hcall _ _ _ _ _ hel hfl _ ha _ hb).2.2 _ hev)

/-- Progress: no expression that checks goes wrong, under any environment the context it checks in
describes.

`Eval.hasType`'s counterpart, and stated under the same two hypotheses: the environment agrees with
the context, and the expression has a type under that context extended with the globals' signatures.

A property of `td` rather than a theorem, because it is not proved: see the module docstring for
what a proof of it still needs. -/
@[expose] public def Progress (td : TypeDecls) : Prop :=
  ∀ (env : Env) (ctx : Context) (e : Expression) (t : Ty),
    Env.HasType td env ctx →
      e.infer td (ctx ++ Globals.types env.globals) = some t → ¬Stuck td env e


/-- A struct of two `int` fields: the smallest declaration two values of one type can be written
against in two different orders. -/
@[expose] public def Stuck.pairDecls : TypeDecls :=
  { ss := Structs.ofDecls [⟨"P", [("a", .int), ("b", .int)]⟩] }

/-- Two `P`s with the same fields bound to the same values, written in opposite orders, compared. -/
@[expose] public def Stuck.pairEquals : Expression :=
  .equals (.structNew "P" [("a", .intLit 1), ("b", .intLit 2)])
    (.structNew "P" [("b", .intLit 2), ("a", .intLit 1)])

/-- It checks: both operands are of the one struct type, and that type is comparable — the fields it
declares are `int`s, so the walk `Ty.comparable` does reaches no function type and no hashmap. -/
public theorem Stuck.infer_pairEquals :
    Stuck.pairEquals.infer Stuck.pairDecls [] = some .bool :=
  Expression.infer_equals_eq_some.mpr
    ⟨.struct "P",
      Expression.infer_structNew_eq_some.mpr
        ⟨_, [("a", .int), ("b", .int)], rfl, by simp,
          Expression.fieldsComplete_eq_true.mpr ⟨by decide, by simp [List.lookup]⟩, rfl⟩,
      Expression.infer_structNew_eq_some.mpr
        ⟨_, [("b", .int), ("a", .int)], rfl, by simp,
          Expression.fieldsComplete_eq_true.mpr ⟨by decide, by simp [List.lookup]⟩, rfl⟩,
      by decide, rfl⟩

/-- A `structNew` of two `int` literals has the one value: its fields under the names they were
written under, holding what the literals evaluate to.

The names are what `EStructNew`'s first premise pins down and the values are what its second
evaluates, so this is the rule read backwards — which is what taking `Stuck.equalsIncomparable`
apart needs, since that rule speaks of the values its operands produced. -/
private theorem Stuck.eq_of_eval_pairNew {name : String} {f g : FieldName} {i j : Int} {v : Value}
    (h : Eval Stuck.pairDecls ∅ (.structNew name [(f, .intLit i), (g, .intLit j)]) v) :
    v = .struct name [(f, .int i), (g, .int j)] := by
  cases h with
  | @EStructNew fvs _ _ _ hnames hev =>
    rcases fvs with _ | ⟨p, _ | ⟨q, _ | ⟨r, rest⟩⟩⟩
    · simp at hnames
    · simp at hnames
    · obtain ⟨f', v₁⟩ := p
      obtain ⟨g', v₂⟩ := q
      obtain ⟨rfl, rfl⟩ : f = f' ∧ g = g' := by simpa using hnames
      cases hev ((f, .intLit i), (f, v₁)) (by simp)
      cases hev ((g, .intLit j), (g, v₂)) (by simp)
      rfl
    · simp at hnames

/-- And it evaluates: both operands produce a struct value, and comparing the two now has an answer
— `true`, since the fields are matched by the names they were written under rather than by where
they were written. -/
public theorem Stuck.eval_pairEquals : Eval Stuck.pairDecls ∅ Stuck.pairEquals (.bool true) := by
  refine
    .EEquals (v₁ := .struct "P" [("a", .int 1), ("b", .int 2)])
      (v₂ := .struct "P" [("b", .int 2), ("a", .int 1)]) _ _ (.EStructNew _ _ rfl ?_)
      (.EStructNew _ _ rfl ?_) rfl
  all_goals
    rintro ⟨p, q⟩ hp
    simp at hp
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := hp
    · exact .EIntLit _
    · exact .EIntLit _

/-- So it is not stuck, which is what the counterexample to `Progress` came to.

Taking the relation apart is what says so, and there are three ways it could have held: either
operand stuck, which is a field's expression stuck and an `intLit` is not, or the comparison without
an answer, which is what the fix removed. -/
public theorem Stuck.not_stuck_pairEquals : ¬Stuck Stuck.pairDecls ∅ Stuck.pairEquals := by
  rintro h
  cases h with
  | equalsLeft hl | equalsRight hl =>
    cases hl with
    | structNewField hp hs =>
      rcases List.mem_cons.mp hp with rfl | hp'
      · cases hs
      · rcases List.mem_cons.mp hp' with rfl | hp''
        · cases hs
        · simp at hp''
  | equalsIncomparable h₁ h₂ hb =>
    obtain rfl := Stuck.eq_of_eval_pairNew h₁
    obtain rfl := Stuck.eq_of_eval_pairNew h₂
    simp [Value.beq?, Value.beqFields?, FieldValues.extract?] at hb
