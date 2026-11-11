module

public import LgtmDeepLean.Lang.Eval

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

/-! ## The shapes a rule asks of a value

One predicate per `Value` constructor that a rule of `Eval` pattern matches on.  A mismatch rule
negates one of these: `¬v.IsBool` is what leaves a conditional stuck on a condition neither
`EIteTrue` nor `EIteFalse` accepts. -/

/-- `v` is a `bool`: what a conditional asks of its condition, `boolAnd` and `boolOr` of their
operands, and `listSortBy` of what its comparison answered. -/
@[expose] public def Value.IsBool (v : Value) : Prop := ∃ b, v = .bool b

/-- `v` is an `int`: what `plus` and `minus` ask of their operands. -/
@[expose] public def Value.IsInt (v : Value) : Prop := ∃ i, v = .int i

/-- `v` is an option: what `optionMatch` asks of its scrutinee. -/
@[expose] public def Value.IsOption (v : Value) : Prop := ∃ o, v = .option o

/-- `v` is a list: what the list forms ask of their first operand, and `listFlatMap` of what each of
its calls produced. -/
@[expose] public def Value.IsList (v : Value) : Prop := ∃ vs, v = .list vs

/-- `v` is a hashmap: what the hashmap forms ask of their first operand. -/
@[expose] public def Value.IsHashmap (v : Value) : Prop := ∃ kvs, v = .hashmap kvs

/-- `v` is a tuple: what `tupleGet` asks of its operand. -/
@[expose] public def Value.IsTuple (v : Value) : Prop := ∃ vs, v = .tuple vs

/-- `v` is a closure: what a call asks of its function, and every form that calls one per element or
per binding asks of its second operand. -/
@[expose] public def Value.IsClosure (v : Value) : Prop :=
  ∃ cbindings cglobals ps body, v = .closure cbindings cglobals ps body

/-- `v` is a struct value: what `structGet` and `structUpdate` ask of their operand. -/
@[expose] public def Value.IsStruct (v : Value) : Prop := ∃ name fvs, v = .struct name fvs

/-- `v` is a value of an inductive type: what `indMatch` asks of its scrutinee. -/
@[expose] public def Value.IsInd (v : Value) : Prop := ∃ name c vs, v = .ind name c vs

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
