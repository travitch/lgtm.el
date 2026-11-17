module

public import LgtmDeepLean.Lang.IR
public import LgtmDeepLean.Lang.TypeCheck
public import LgtmDeepLean.Lang.Value

/-! # Evaluation

The relational semantics of the IR, and its soundness: evaluating a well-typed expression produces
a value of the type inferred for it.  Values, environments, and what it means for either to have a
type live in `Value.lean`. -/

/-- This is a relational evaluator for expressions under a given `Env` (environment).

This is the bridge from the deeply-embedded DSL to logical terms we can reason about
using standard Lean techniques.  The `Expression` is the DSL term while the `Value` is
how it would be evaluated in Lean.  Proofs are over the latter, which can use the full
Lean standard library.

`td` is carried only so that `EApp` can state `ArgsHaveType`: nothing here consults a type
declaration to compute anything.  A `structNew` is a name and the values its fields were given, a
`structGet` reads a field out of the value it finds, and a `structUpdate` rebinds the fields it names,
so evaluation needs no more of a struct than the value carries.  An `indNew` and an `indMatch` are
the same: the value carries the constructor it was built by, which is all the match needs to find its
alternative.  Whether that agrees with the declaration is the type checker's business, and
`Eval.hasType` is where the two meet. -/
public inductive Eval (td : TypeDecls) : Env → Expression → Value → Prop where
  |
  ELam (ps : List (String × Ty)) (body : Expression) :
    Eval td env (.lam ps body) (env.closure ps body)
  /-- A call evaluates its function and its arguments, then the body in the closure's environment
extended with the parameters. -/
  |
  EApp (f : Expression) (args : List Expression) :
    Eval td env f (.closure cbindings cglobals ps body) →
      args.length = vs.length →
      (∀ p ∈ args.zip vs, Eval td env p.1 p.2) →
      ArgsHaveType td ps vs →
      Eval td (Env.extend ⟨cbindings, cglobals⟩ ps vs) body v → Eval td env (.app f args) v
  | EBoolLit (b : Bool) : Eval td env (.boolLit b) (.bool b)
  /-- A conditional whose condition came out `true` evaluates its first branch, and one whose condition
came out `false` its second.

Two rules rather than one over a `Bool`, so that a proof taking an `ite` apart is left with the branch
that ran rather than with an `if` to reduce, and so that the branch not taken is not mentioned at all:
it is never evaluated, which is the whole of what a conditional does that a two-argument function
could not.

A condition that evaluates to anything but a `bool` leaves this stuck — the only thing that can go
wrong here, and exactly what typing rules out. -/
  |
  EIteTrue (c thn els : Expression) :
    Eval td env c (.bool true) → Eval td env thn v → Eval td env (.ite c thn els) v
  |
  EIteFalse (c thn els : Expression) :
    Eval td env c (.bool false) → Eval td env els v → Eval td env (.ite c thn els) v
  |
  EBoolAndFalse (l r : Expression) :
    Eval td env l (.bool false) → Eval td env (.boolAnd l r) (.bool false)
  |
  EBoolAndTrue (l r : Expression) :
    Eval td env l (.bool true) → Eval td env r (.bool b) → Eval td env (.boolAnd l r) (.bool b)
  |
  EBoolOrTrue (l r : Expression) :
    Eval td env l (.bool true) → Eval td env (.boolOr l r) (.bool true)
  |
  EBoolOrFalse (l r : Expression) :
    Eval td env l (.bool false) → Eval td env r (.bool b) → Eval td env (.boolOr l r) (.bool b)
  /-- A comparison evaluates both of its operands and hands back what comparing the two values said.

The comparison itself is `Value.beq?`, which is a function on values and mentions nothing about
evaluation; the premise is what makes a pair it has no answer for stuck.  That is a closure on either
side, or two values that disagree about the type they carry — the only things that can go wrong here,
and exactly what `Ty.comparable` and the two operands sharing a type rule out between them.

Both operands are always evaluated, unlike a conditional's branches: a comparison is a comparison of
two values, so neither is in a position to make the other unnecessary even where the answer would be
the same.

One rule rather than the two `ite` has, because what a proof is left with here is not a choice
between branches but the two values and what `Value.beq?` said about them — which
`Value.equiv_of_beq?` turns into `Value.Equiv`, Lean's own equality up to the order a struct carries
its fields in, and `Value.ne_of_beq?` into Lean's own `≠`. -/
  |
  EEquals (l r : Expression) :
    Eval td env l v₁ →
      Eval td env r v₂ → Value.beq? v₁ v₂ = some b → Eval td env (.equals l r) (.bool b)
  /-- An ordering evaluates both of its operands and hands back what comparing the two values said,
exactly as `EEquals` does, with `Value.lt?` in place of `Value.beq?`.

The premise is what makes a pair the comparison has no answer for stuck: a value of a type with no
ordering on either side — a `bool` and a hashmap among them, which `Value.beq?` does answer for — or
two values that disagree about the type they carry.  Those are the only things that can go wrong
here, and exactly what `Ty.orderable` and the two operands sharing a type rule out between them. -/
  |
  ELt (l r : Expression) :
    Eval td env l v₁ → Eval td env r v₂ → Value.lt? v₁ v₂ = some b → Eval td env (.lt l r) (.bool b)
  /-- The same rule read one answer wider: `Value.le?` and `Value.lt?` are one comparison, and which
of them a pair of equal values satisfies is the whole of what the two forms differ in. -/
  |
  ELe (l r : Expression) :
    Eval td env l v₁ → Eval td env r v₂ → Value.le? v₁ v₂ = some b → Eval td env (.le l r) (.bool b)
  /-- Let binds a variable that shadows any existing bindings.

    The bound value is available in the body of the let.  This is a non-recursive let. -/
  |
  ELet (x : String) (e : Expression) (body : Expression) :
    Eval td env e v₁ →
      Eval td ⟨(x, v₁) :: env.bindings, env.globals⟩ body v → Eval td env (.let_ x e body) v
  | EVarRef (x : String) : env.lookup x = some v → Eval td env (.varRef x) v
  /-- Building a struct evaluates each field's expression and keeps the result under that field's name.

The fields come out under the names they went in under and in the order they went in, which is what
`fes.map Prod.fst = fvs.map Prod.fst` says; the premise over the zip is then one evaluation per
field, the way `EApp`'s is one per argument.  Which names those are is not checked here — the
declaration is not consulted — so a `structNew` naming fields the struct does not have still
evaluates.  Being ill typed is what rules it out. -/
  |
  EStructNew (name : String) (fes : List (FieldName × Expression)) :
    fes.map Prod.fst = fvs.map Prod.fst →
      (∀ p ∈ fes.zip fvs, Eval td env p.1.2 p.2.2) →
      Eval td env (.structNew name fes) (.struct name fvs)
  /-- Reading a field evaluates the struct and hands back what that field is bound to.

Bound in the *value*, not declared in the struct: a field the value does not carry leaves this stuck,
which is the only thing that can go wrong here and is exactly what typing rules out. -/
  |
  EStructGet (e : Expression) (f : FieldName) :
    Eval td env e (.struct name fvs) → fvs.lookup f = some v → Eval td env (.structGet e f) v
  /-- Updating a struct evaluates it, evaluates each new field value, and rebinds those fields.

`FieldValues.update` rebinds in place, so the result carries the same fields in the same order as the
struct it came from and differs only in what the named ones hold.  Fields the update names that the
struct does not have are therefore dropped rather than added — again a case typing rules out. -/
  |
  EStructUpdate (e : Expression) (fes : List (FieldName × Expression)) :
    Eval td env e (.struct name fvs) →
      fes.map Prod.fst = us.map Prod.fst →
      (∀ p ∈ fes.zip us, Eval td env p.1.2 p.2.2) →
      Eval td env (.structUpdate e fes) (.struct name (FieldValues.update fvs us))
  /-- Applying a constructor evaluates one expression per data type it takes and keeps the values in
the order they were given, which is the order the constructor takes them in.

The premise is one evaluation per argument, the way `EStructNew`'s is one per field and `EApp`'s is
one per argument, with the lengths pinned down separately because `List.zip` stops at the shorter
list.  The two names are carried through as they were written: nothing here says the type has such a
constructor, or that it takes as many arguments as it was given.  Being ill typed is what rules those
out. -/
  |
  EIndNew (name : String) (c : CtorName) (args : List Expression) :
    args.length = vs.length →
      (∀ p ∈ args.zip vs, Eval td env p.1 p.2) → Eval td env (.indNew name c args) (.ind name c vs)
  /-- A match evaluates its scrutinee, takes the alternative for the constructor that built the value,
binds that alternative's names to the values the constructor carries, and evaluates its expression.

The alternative is found by name, so nothing here depends on where the declaration put a constructor
or on where the match put the alternative for it — which is how `Expression.inferAlts` reads them too,
resolving each alternative's constructor by name.  A match with no alternative for the value it was
handed is stuck, which is exactly what the exhaustiveness the type checker insists on rules out.

The names are bound the way a call binds its parameters — in front of the environment, so they shadow
it, and by `List.zip`, so a name repeated in one alternative takes the value of its leftmost
occurrence.  They are the alternative's own names: nothing about them survives into the value, which
is why the *type* of each has to come from the declaration when `Eval.hasType` types this. -/
  |
  EIndMatch (scrut : Expression) (alts : List (CtorName × List String × Expression)) :
    Eval td env scrut (.ind name c vs) →
      alts.lookup c = some (xs, body) →
      Eval td ⟨xs.zip vs ++ env.bindings, env.globals⟩ body v → Eval td env (.indMatch scrut alts) v
  | EIntLit (i : Int) : Eval td env (.intLit i) (.int i)
  |
  EPlus (e₁ : Expression) (e₂ : Expression) :
    Eval td env e₁ (.int n₁) → Eval td env e₂ (.int n₂) → Eval td env (.plus e₁ e₂) (.int (n₁ + n₂))
  |
  EMinus (e₁ : Expression) (e₂ : Expression) :
    Eval td env e₁ (.int n₁) →
      Eval td env e₂ (.int n₂) → Eval td env (.minus e₁ e₂) (.int (n₁ - n₂))
  /-- The smaller and the larger of two `int`s, which is `Int`'s own `min` and `max`: both operands
are evaluated, the way `EPlus`'s are, so neither form short-circuits on an operand that already
settles the answer. -/
  |
  EMin (e₁ : Expression) (e₂ : Expression) :
    Eval td env e₁ (.int n₁) →
      Eval td env e₂ (.int n₂) → Eval td env (.min e₁ e₂) (.int (min n₁ n₂))
  |
  EMax (e₁ : Expression) (e₂ : Expression) :
    Eval td env e₁ (.int n₁) →
      Eval td env e₂ (.int n₂) → Eval td env (.max e₁ e₂) (.int (max n₁ n₂))
  | EStringLit (s : String) : Eval td env (.stringLit s) (.string s)
  /-- An empty option evaluates to the empty value, and its annotation goes nowhere: a value carries no
type, so what the annotation is for is `Expression.infer` alone — exactly as `ENil` drops `lnil`'s. -/
  | ENone (ty : Ty) : Eval td env (.optionNone ty) (.option none)
  | ESome (e : Expression) : Eval td env e v → Eval td env (.optionSome e) (.option (some v))
  /-- A match on an option that came out empty evaluates its first case, and one on an option holding a
value binds that value to the name the second case gives and evaluates that.

Two rules rather than one, the way `ite` has two: a proof taking one apart is left with the case that
ran, and the case that did not run is not mentioned at all — only one of them is ever evaluated.

They are also the two rules `EIndMatch` is one rule for.  A `match` on an inductive type finds its
alternative by the constructor name the value carries, which is a lookup that may fail; an option has
two cases and the value is one of them, so there is nothing to resolve and no way for a match on an
option value to be stuck.  A scrutinee that evaluates to something that is not an option is the only
thing that can go wrong here, and that is what typing rules out.

The name is bound in front of the environment, so it shadows what was there, the way a `let`'s is. -/
  |
  EOptionMatchNone (scrut nbody : Expression) (x : String) (sbody : Expression) :
    Eval td env scrut (.option none) →
      Eval td env nbody v → Eval td env (.optionMatch scrut nbody x sbody) v
  |
  EOptionMatchSome (scrut nbody : Expression) (x : String) (sbody : Expression) :
    Eval td env scrut (.option (some w)) →
      Eval td ⟨(x, w) :: env.bindings, env.globals⟩ sbody v →
      Eval td env (.optionMatch scrut nbody x sbody) v
  | ENil (ty : Ty) : Eval td env (.lnil ty) (.list [])
  |
  ECons (e₁ : Expression) (e₂ : Expression) :
    Eval td env e₁ v → Eval td env e₂ (.list vs) → Eval td env (.lcons e₁ e₂) (.list (v :: vs))
  /-- A match on an empty list evaluates its first case, and one on a list with a head evaluates its
second with the head and the tail bound to the names that case gives them.

The two rules `EOptionMatchNone` and `EOptionMatchSome` are, read over a list, and two rather than one
for the same reason: only one of the cases is ever evaluated, so the one that did not run is not
mentioned at all.  What the non-empty case adds is the *second* name — a list's tail is a list, where
an option holds a value and nothing else — and that tail is a `.list` put back together out of what
was left, which is the one thing either rule builds rather than takes apart.

The names are bound in front of the environment, the head in front of the tail, so each shadows what
was there the way a `let`'s does and a case binding one name twice reads it as the head.  A scrutinee
that evaluates to something that is not a list is the only thing that can go wrong here, and that is
what typing rules out. -/
  |
  EListMatchNil (scrut nbody : Expression) (hd tl : String) (cbody : Expression) :
    Eval td env scrut (.list []) →
      Eval td env nbody v → Eval td env (.listMatch scrut nbody hd tl cbody) v
  |
  EListMatchCons (scrut nbody : Expression) (hd tl : String) (cbody : Expression) :
    Eval td env scrut (.list (w :: ws)) →
      Eval td ⟨(hd, w) :: (tl, .list ws) :: env.bindings, env.globals⟩ cbody v →
      Eval td env (.listMatch scrut nbody hd tl cbody) v
  /-- An index evaluates the list and the index and hands back the option of what the list holds at
that position.

One rule rather than the two a match on a list has, and for the reason `EHashmapGet` is one:
`Value.index?` is a function on a list and a position that answers for both cases, so a proof is left
with the list, the index, and what that said about the two rather than with a case to choose.  An
index the list has no element at is not among the things that can go wrong — it is the empty option,
which is a value like any other, exactly as a key the map does not bind is.

Both operands are always evaluated, the way a comparison's two are: neither is in a position to make
the other unnecessary.  Unlike a get there is no premise beyond them, since nothing is compared — the
lookup is total, so a non-list first operand and a non-`int` second are the only things that can go
wrong here, and that is what typing rules out. -/
  |
  EListIndex (l i : Expression) :
    Eval td env l (.list vs) →
      Eval td env i (.int n) → Eval td env (.listIndex l i) (.option (Value.index? vs n))
  /-- Map `f` over `e` (of type List α).

The length equality clause is a guarantee that the result list is always
the same length as the input. -/
  |
  EListMap (e f : Expression) :
    Eval td env e (.list vs) →
      Eval td env f (.closure cbindings cglobals ps body) →
      vs.length = vs'.length →
      (∀ p ∈ vs.zip vs', ArgsHaveType td ps [p.1]) →
      (∀ p ∈ vs.zip vs', Eval td (Env.extend ⟨cbindings, cglobals⟩ ps [p.1]) body p.2) →
      Eval td env (.listMap e f) (.list vs')
  /-- A flat mapping over a list is `EListMap`'s call per element with the results run together: each
call produces a list, and what comes back is those lists one after another.

`vss` is a `List (List Value)` where a mapping's `vs'` is a `List Value`, and that is the whole of
the difference between the two rules.  The lengths that agree are still the operand's and the calls'
— one list produced per element — so the premises line up premise for premise; `List.flatten` is
what then makes the result a list of elements again, and it is a function rather than a premise for
the reason `Value.sortByKey` is one: the order the pieces go in is settled by the list that was
given, so there is nothing for a premise to pin down.

The length is what no premise mentions, unlike `EListMap`, whose first premise over the elements is
exactly the guarantee that the result is as long as its operand.  A call returning the empty list
drops its element and one returning several puts several in its place, which is what a mapping
cannot do and what this form is for.

The calls are `EListMap`'s otherwise: the element is the one argument, `ArgsHaveType` holds it to
the closure's parameter, and the body is evaluated in the environment the closure captured.  What
each one must produce is a `.list`, which is the one thing asked of a call's result here and is what
typing guarantees. -/
  |
  EListFlatMap (e f : Expression) :
    Eval td env e (.list vs) →
      Eval td env f (.closure cbindings cglobals ps body) →
      vs.length = vss.length →
      (∀ p ∈ vs.zip vss, ArgsHaveType td ps [p.1]) →
      (∀ p ∈ vs.zip vss, Eval td (Env.extend ⟨cbindings, cglobals⟩ ps [p.1]) body (.list p.2)) →
      Eval td env (.listFlatMap e f) (.list vss.flatten)
  /-- A length evaluates the list and hands back how many elements it has, as an `int`.

`List.length` is a `Nat` and `Value.int` holds an `Int`, so the count is cast on the way out: the IR
has no natural number type, and a length is one of the few places a `Nat` would otherwise appear.
The cast is total and loses nothing — a length is never negative — which is why this needs no premise
beyond evaluating the operand.

The elements are not looked at, only counted, so unlike `EListReverse` this is a rule whose result
mentions none of them.  A non-list operand leaves it stuck, which is the only thing that can go
wrong here and is exactly what typing rules out. -/
  |
  EListLength (e : Expression) :
    Eval td env e (.list vs) → Eval td env (.listLength e) (.int (vs.length : Int))
  /-- A search evaluates the list and the predicate, calls the predicate on the elements in order,
and hands back the index of the first one that answered `true`.

Two rules rather than one, the way `ite` has two: the value is an option, and which of its two shapes
it is is what the calls answered.  `pre ++ w :: post` is what says *first* — every element before `w`
answered `false`, `w` answered `true`, and how many came before it is the index.

`post` is the one thing no premise speaks of, and that is the short circuit: the elements after the
match are never handed to the predicate, so a search whose predicate would be stuck on one of them
has a value anyway.  That is where this parts company with `EListSortBy`, whose comparison must
answer for every pair of elements it is asked about.

The calls are `EListMap`'s otherwise: the element is the one argument, `ArgsHaveType` holds it to the
closure's parameter, and the body is evaluated in the environment the closure captured.  What each one
must produce is a `.bool`, which is the one thing asked of a call's result here and is what typing
guarantees.

The index is a `Nat` cast to the `Int` a `Value.int` holds, exactly as `EListLength`'s count is: the
IR has no natural number type, and a position is never negative. -/
  |
  EListFindIndexSome (e f : Expression) :
    Eval td env e (.list (pre ++ w :: post)) →
      Eval td env f (.closure cbindings cglobals ps body) →
      (∀ u ∈ pre, ArgsHaveType td ps [u]) →
      (∀ u ∈ pre, Eval td (Env.extend ⟨cbindings, cglobals⟩ ps [u]) body (.bool false)) →
      ArgsHaveType td ps [w] →
      Eval td (Env.extend ⟨cbindings, cglobals⟩ ps [w]) body (.bool true) →
      Eval td env (.listFindIndex e f) (.option (some (.int (pre.length : Int))))
  /-- And a search that found nothing: every element answered `false`, so there is no index and the
value is the empty option.

This is the one of the two rules that speaks for the whole list, where the other stops at the first
match — a search that finds nothing is the search that has been made to look at every element. -/
  |
  EListFindIndexNone (e f : Expression) :
    Eval td env e (.list vs) →
      Eval td env f (.closure cbindings cglobals ps body) →
      (∀ u ∈ vs, ArgsHaveType td ps [u]) →
      (∀ u ∈ vs, Eval td (Env.extend ⟨cbindings, cglobals⟩ ps [u]) body (.bool false)) →
      Eval td env (.listFindIndex e f) (.option none)
  |
  EListReverse (e : Expression) :
    Eval td env e (.list vs) → Eval td env (.listReverse e) (.list vs.reverse)
  /-- A sort evaluates the list and the projection, calls the projection once per element to get that
element's key, and hands the elements back in the order their keys put them in.

The calls are `EListMap`'s, premise for premise: one argument apiece, `ArgsHaveType` holding the
element to the closure's parameter rather than entering a function it was not written for, and the
body evaluated in the environment the closure captured rather than in the one the sort was written
in.  What they produce is where the two forms part company — a key rather than an element.  The keys
go into `Value.sortByKey` and nowhere else, and what comes back out is the list that went in,
reordered: a sort is the one list form that calls a function per element and still returns a list of
the type it was given.

`Value.sortByKey` is stable, so the elements of equal keys come back in the order they were in.

The last premise is what makes a pair of keys the comparison has no answer for stuck, the way
`ELt`'s is, and it is over the keys rather than over the elements: `Ty.orderable` is asked of the
projection's result type and of nothing else, so the elements are of no type the ordering has to
reach the bottom of. -/
  |
  EListSortOn (e f : Expression) :
    Eval td env e (.list vs) →
      Eval td env f (.closure cbindings cglobals ps body) →
      vs.length = ks.length →
      (∀ p ∈ vs.zip ks, ArgsHaveType td ps [p.1]) →
      (∀ p ∈ vs.zip ks, Eval td (Env.extend ⟨cbindings, cglobals⟩ ps [p.1]) body p.2) →
      (∀ k ∈ ks, ∀ k' ∈ ks, (Value.cmp? k k').isSome) →
      Eval td env (.listSortOn e f) (.list ((Value.sortByKey (vs.zip ks)).map Prod.fst))
  /-- A sort by a comparison evaluates the list and the comparison, calls the comparison on each pair
of elements, and hands the elements back in the order those answers put them in.

`cmp` is the function the whole rule turns on: `Value.sortWith` needs a `Value → Value → Bool` and a
DSL function is not one, so the rule asks for a Lean function and then holds it to the DSL one —
`Eval ... body (.bool (cmp a b))` at every pair of elements is what says the two agree.  A comparison
that gets stuck on some pair of them is a sort with no such `cmp` to be had, and so no value, exactly
as `EListSortOn` has none where a key cannot be compared.  Over pairs rather than over the elements
singly, which is what sets this apart from every other rule that calls a function: a key is read off
one element and a comparison is asked about two.

Only pairs drawn from the list are spoken for, which is all `mergeSort` ever asks about; what `cmp`
answers elsewhere decides nothing.

The calls are `EListSortOn`'s otherwise, premise for premise: `ArgsHaveType` holding the two
elements to the closure's parameters rather than entering a function they do not fit, and the body
evaluated in the environment the closure captured.  There is no premise over the answers, where
`EListSortOn` has one over the keys: a `bool` is the answer and there is nothing further to compare.

`Value.sortWith` is stable, so elements the comparison does not separate come back in the order they
were in. -/
  |
  EListSortBy (e f : Expression) :
    Eval td env e (.list vs) →
      Eval td env f (.closure cbindings cglobals ps body) →
      (∀ a ∈ vs, ∀ b ∈ vs, ArgsHaveType td ps [a, b]) →
      (∀ a ∈ vs,
        ∀ b ∈ vs, Eval td (Env.extend ⟨cbindings, cglobals⟩ ps [a, b]) body (.bool (cmp a b))) →
      Eval td env (.listSortBy e f) (.list (Value.sortWith cmp vs))
  /-- The empty hashmap, binding nothing.  Its two annotations go nowhere, for the reason `ENil` drops
`lnil`'s and `ENone` drops `optionNone`'s: a value carries no type, so what they are for is
`Expression.infer` alone. -/
  | EHashmapEmpty (kt vt : Ty) : Eval td env (.hashmapEmpty kt vt) (.hashmap [])
  /-- A put evaluates the map, the key and the value, and rebinds: the new binding on the front of
what the map had with any binding for that key dropped.

All three are always evaluated, the way a comparison's two operands are: none of them is in a
position to make another unnecessary.

`KeyValues.erase?` is where the keys are compared, and its `none` is what leaves this stuck — a key
in the map that the new one cannot be compared with, which is the only thing that can go wrong here
and is exactly what `Ty.comparable` on the key type rules out.  Putting the new binding on the front
of an *erase* rather than in place is what makes this a map rather than a stack of shadowed
bindings: a key is bound once, so there is never a later binding for `KeyValues.lookup?` to walk
past. -/
  |
  EHashmapPut (m k v : Expression) :
    Eval td env m (.hashmap kvs) →
      Eval td env k vk →
      Eval td env v vv →
      KeyValues.erase? kvs vk = some kvs' →
      Eval td env (.hashmapPut m k v) (.hashmap ((vk, vv) :: kvs'))
  /-- A get evaluates the map and the key and hands back the option of what that key is bound to.

One rule rather than the two `optionMatch` has, and for the reason `EEquals` is one rule: what a
proof is left with here is not a choice between branches but the map, the key, and what
`KeyValues.lookup?` said about the two.  A key the map does not bind is not one of the things that
can go wrong — it is the empty option, which is a value like any other — and the `none` that leaves
this stuck is the one a put's does. -/
  |
  EHashmapGet (m k : Expression) :
    Eval td env m (.hashmap kvs) →
      Eval td env k vk →
      KeyValues.lookup? kvs vk = some o → Eval td env (.hashmapGet m k) (.option o)
  /-- A mapping evaluates the map and the function, then calls that function once per binding — the
key and the value it is bound to as the two arguments — and binds the key to what the call produced.

The keys are the map's own, which is what `kvs.map Prod.fst = kvs'.map Prod.fst` says: a mapping
rebinds no key, drops no binding and introduces none, so nothing is compared and this needs no
`KeyValues` premise, exactly as `EHashmapToList` needs none.  The order is the map's too, for the
same reason a conversion's is — one value apiece is replaced and nothing is moved.

The two premises over the zip are `EApp`'s two, one per binding: `ArgsHaveType` is what makes a
function the key and the value do not fit stuck rather than entered with arguments it was not
written for, and the body is evaluated in the environment the closure captured extended with its
parameters, which is where a call evaluates it.  A second operand that evaluates to something other
than a closure is the only other thing that can go wrong here, and that is what typing rules out. -/
  |
  EHashmapMap (m f : Expression) :
    Eval td env m (.hashmap kvs) →
      Eval td env f (.closure cbindings cglobals ps body) →
      kvs.map Prod.fst = kvs'.map Prod.fst →
      (∀ p ∈ kvs.zip kvs', ArgsHaveType td ps [p.1.1, p.1.2]) →
      (∀ p ∈ kvs.zip kvs',
        Eval td (Env.extend ⟨cbindings, cglobals⟩ ps [p.1.1, p.1.2]) body p.2.2) →
      Eval td env (.hashmapMap m f) (.hashmap kvs')
  /-- A `toList` evaluates the map and hands its bindings back as a list, one two-element tuple per
binding: the key beside the value it is bound to.

Nothing is compared and nothing can go wrong, so this is the one hashmap rule with no `KeyValues`
premise — the bindings are already the list this produces, and the walk is `List.map` over them.

The order is the map's own, which is the order the bindings were put in: `Value.hashmap` canonicalizes
nothing, so two maps binding the same keys to the same values convert to lists that differ whenever
they were built in different orders.  That is the same fact `Ty.comparable` turns a hashmap type down
for, and converting does not escape it — `tuple [kt, vt]` is comparable where `hashmap kt vt` is not,
but what two converted maps then compare equal is the bindings *and* their order. -/
  |
  EHashmapToList (m : Expression) :
    Eval td env m (.hashmap kvs) →
      Eval td env (.hashmapToList m) (.list (kvs.map fun p => .tuple [p.1, p.2]))
  /-- Building a tuple evaluates one expression per element and keeps the values in the order they
were given, which is the order the type the expression is inferred at gives them.

The premise is one evaluation per element with the lengths pinned down separately, the way
`EIndNew`'s is one per argument and for the same reason: both are positional, and `List.zip` stops
at the shorter list.  Nothing here says how many elements there ought to be, which is the one way
this is easier than `EIndNew` — a constructor's arity is its declaration's, where a tuple's length
is read off the elements themselves. -/
  |
  ETupleNew (es : List Expression) :
    es.length = vs.length →
      (∀ p ∈ es.zip vs, Eval td env p.1 p.2) → Eval td env (.tupleNew es) (.tuple vs)
  /-- Reading an element evaluates the tuple and hands back the value at that position.

Read out of the *value*, as `EStructGet`'s field is: an index the value has nothing at leaves this
stuck, which is the only thing that can go wrong here and is exactly what typing rules out.  The
index is a `Nat` in the expression rather than something to evaluate, so there is no premise for it
— the position is settled before anything runs, which is what let `Expression.infer` read the type
at it. -/
  |
  ETupleGet (e : Expression) (i : Nat) :
    Eval td env e (.tuple vs) → vs[i]? = some v → Eval td env (.tupleGet e i) v

/-! `Expression.unreachable` is the one form with no rule above, and the omission is the whole of
what the form is.  Every other way to be stuck is something typing rules out — a condition that is
not a `bool`, a field the value does not carry, a match with no alternative for the constructor it
was handed.  This one is stuck for a well-typed expression too, which is what makes reaching it
something a proof has to rule out rather than something the type checker already did. -/

/-- An `unreachable` has no value.

This is what a use of the form is proved safe by.  `Eval td env e v` is a premise everywhere in this
development — `FuncDecl.Apply` asks for one, and so does every theorem about a declaration — so a
proof that a call returns anything at all is a proof that no `unreachable` on the branches it took
was reached.  A branch that cannot be shown unreachable is one no such proof goes through, rather
than one that produces a wrong answer.

Neither the annotation nor the message appears in what this says: there is no evaluation here for
either to be carried by. -/
public theorem Eval.not_unreachable {td : TypeDecls} {env : Env} {t : Ty} {why : String}
    {v : Value} : ¬Eval td env (.unreachable t why) v := by
  rintro h
  cases h

/-! ## Inversion

The rules read backwards: a value the whole form produced, taken apart into the values its
subexpressions produced.  This is what a proof about a declaration works from — `Eval` is a
relation, so a theorem about a call starts from the one premise that it has a value at all and
unpicks it form by form — and these are the same inversion principles `Expression.infer_*_eq_some`
are for the type checker, which is the other relation stated over an `Expression`.

One per form, each with the premises of its rule as an existential over whatever that rule left
implicit.  No form below needs a hypothesis to say which rule applied: the expression determines the
rule, so a value for the form is a value from that rule and nothing else.  `optionMatch` is the one
exception — it has two rules — and the version here is for the shape the model writes, an
`unreachable` on the empty case, which `Eval.not_unreachable` rules out.

`ArgsHaveType` premises are dropped: they are what makes a call with ill-typed arguments stuck, and
nothing a proof of what a call *returned* has further use for.  A caller that wants them can still
`cases` the evaluation itself. -/

public theorem Eval.varRef_inv {td : TypeDecls} {env : Env} {x : String} {v : Value}
    (h : Eval td env (.varRef x) v) : env.lookup x = some v := by
  cases h with
  | EVarRef _ hx => exact hx

public theorem Eval.lam_inv {td : TypeDecls} {env : Env} {ps : List (String × Ty)}
    {body : Expression} {v : Value} (h : Eval td env (.lam ps body) v) :
    v = env.closure ps body := by
  cases h with
  | ELam _ _ => rfl

public theorem Eval.let_inv {td : TypeDecls} {env : Env} {x : String} {e body : Expression}
    {v : Value} (h : Eval td env (.let_ x e body) v) :
    ∃ w, Eval td env e w ∧ Eval td ⟨(x, w) :: env.bindings, env.globals⟩ body v := by
  cases h with
  | ELet _ _ _ he hbody => exact ⟨_, he, hbody⟩

/-! The literals and the arithmetic, where a rule reads the value off the operands with no premise
beyond evaluating them.  A literal's inversion is an equation rather than an existential — there is
nothing in it to be found — and the three arithmetic forms hand back the two `Int`s their operands
produced beside what the operation made of them. -/

public theorem Eval.intLit_inv {td : TypeDecls} {env : Env} {i : Int} {v : Value}
    (h : Eval td env (.intLit i) v) : v = .int i := by
  cases h with
  | EIntLit _ => rfl

public theorem Eval.plus_inv {td : TypeDecls} {env : Env} {e₁ e₂ : Expression} {v : Value}
    (h : Eval td env (.plus e₁ e₂) v) :
    ∃ n₁ n₂ : Int, Eval td env e₁ (.int n₁) ∧ Eval td env e₂ (.int n₂) ∧ v = .int (n₁ + n₂) := by
  cases h with
  | EPlus _ _ h₁ h₂ => exact ⟨_, _, h₁, h₂, rfl⟩

public theorem Eval.minus_inv {td : TypeDecls} {env : Env} {e₁ e₂ : Expression} {v : Value}
    (h : Eval td env (.minus e₁ e₂) v) :
    ∃ n₁ n₂ : Int, Eval td env e₁ (.int n₁) ∧ Eval td env e₂ (.int n₂) ∧ v = .int (n₁ - n₂) := by
  cases h with
  | EMinus _ _ h₁ h₂ => exact ⟨_, _, h₁, h₂, rfl⟩

public theorem Eval.min_inv {td : TypeDecls} {env : Env} {e₁ e₂ : Expression} {v : Value}
    (h : Eval td env (.min e₁ e₂) v) :
    ∃ n₁ n₂ : Int, Eval td env e₁ (.int n₁) ∧ Eval td env e₂ (.int n₂) ∧
      v = .int (min n₁ n₂) := by
  cases h with
  | EMin _ _ h₁ h₂ => exact ⟨_, _, h₁, h₂, rfl⟩

public theorem Eval.structGet_inv {td : TypeDecls} {env : Env} {e : Expression} {f : FieldName}
    {v : Value} (h : Eval td env (.structGet e f) v) :
    ∃ name fvs, Eval td env e (.struct name fvs) ∧ fvs.lookup f = some v := by
  cases h with
  | EStructGet _ _ he hf => exact ⟨_, _, he, hf⟩

/-- Reading a field off an operand that carries that field answers with the field and nothing is
left existential: the rule's premise is an evaluation of the operand, so an operand every value of
which binds `f` to `w` is one this form can only produce `w` from.

`Eval.structGet_inv` with both of its existentials spent, which is the form every mismatch rule of
`Stuck` one form further out asks for — those rules speak of the value a subexpression produced, so
refuting one means reading that value rather than evaluating it again.  The hypothesis is over every
value the operand can produce because nothing here makes `Eval` deterministic. -/
public theorem Eval.structGet_eq {td : TypeDecls} {env : Env} {e : Expression} {f : FieldName}
    {w u : Value} (hop : ∀ v, Eval td env e v → v.field? f = some w)
    (h : Eval td env (.structGet e f) u) : u = w := by
  obtain ⟨name', fvs', hev, hf'⟩ := Eval.structGet_inv h
  have hf := hop _ hev
  simp only [Value.field?] at hf
  exact Option.some.inj (hf'.symm.trans hf)

/-- The same at an operand that is a name the environment binds, where the quantifier collapses: a
`varRef` produces the one value the environment holds. -/
public theorem Eval.structGet_varRef_eq {td : TypeDecls} {env : Env} {x : String}
    {v : Value} {f : FieldName} {w u : Value}
    (hx : env.lookup x = some v) (hf : v.field? f = some w)
    (h : Eval td env (.structGet (.varRef x) f) u) : u = w :=
  Eval.structGet_eq (fun _ hu => by
    rw [Option.some.inj ((Eval.varRef_inv hu).symm.trans hx)]; exact hf) h

public theorem Eval.tupleGet_inv {td : TypeDecls} {env : Env} {e : Expression} {i : Nat}
    {v : Value} (h : Eval td env (.tupleGet e i) v) :
    ∃ vs, Eval td env e (.tuple vs) ∧ vs[i]? = some v := by
  cases h with
  | ETupleGet _ _ he hi => exact ⟨_, he, hi⟩

public theorem Eval.tupleNew_inv {td : TypeDecls} {env : Env} {es : List Expression} {v : Value}
    (h : Eval td env (.tupleNew es) v) :
    ∃ vs, v = .tuple vs ∧ es.length = vs.length ∧ ∀ p ∈ es.zip vs, Eval td env p.1 p.2 := by
  cases h with
  | ETupleNew _ hlen hev => exact ⟨_, rfl, hlen, hev⟩

public theorem Eval.hashmapGet_inv {td : TypeDecls} {env : Env} {m k : Expression}
    {o : Option Value} (h : Eval td env (.hashmapGet m k) (.option o)) :
    ∃ kvs vk, Eval td env m (.hashmap kvs) ∧ Eval td env k vk ∧
      KeyValues.lookup? kvs vk = some o := by
  cases h with
  | EHashmapGet _ _ hm hk hlookup => exact ⟨_, _, hm, hk, hlookup⟩

public theorem Eval.hashmapToList_inv {td : TypeDecls} {env : Env} {m : Expression}
    {vs : List Value} (h : Eval td env (.hashmapToList m) (.list vs)) :
    ∃ kvs, Eval td env m (.hashmap kvs) ∧ vs = kvs.map fun p => .tuple [p.1, p.2] := by
  cases h with
  | EHashmapToList _ hm => exact ⟨_, hm, rfl⟩

/-- A match on an option whose empty case is an `unreachable` took the other case: there is no rule
for an `unreachable`, so a value for the match at all is a value for the scrutinee. -/
public theorem Eval.optionMatch_unreachable_inv {td : TypeDecls} {env : Env} {scrut : Expression}
    {t : Ty} {why x : String} {sbody : Expression} {v : Value}
    (h : Eval td env (.optionMatch scrut (.unreachable t why) x sbody) v) :
    ∃ w, Eval td env scrut (.option (some w)) ∧
      Eval td ⟨(x, w) :: env.bindings, env.globals⟩ sbody v := by
  cases h with
  | EOptionMatchNone _ _ _ _ _ hnone => exact absurd hnone Eval.not_unreachable
  | EOptionMatchSome _ _ _ _ hscrut hbody => exact ⟨_, hscrut, hbody⟩

/-- An index inverted is its one rule read backwards: the list, the position, and the option
`Value.index?` made of the two.

No disjunction, unlike `Eval.listFindIndex_inv`: one rule answers for an index the list has an
element at and for one it does not, so what the value is is settled by the function rather than by a
case a proof has to make. -/
public theorem Eval.listIndex_inv {td : TypeDecls} {env : Env} {l i : Expression} {v : Value}
    (h : Eval td env (.listIndex l i) v) :
    ∃ vs n, Eval td env l (.list vs) ∧ Eval td env i (.int n) ∧
      v = .option (Value.index? vs n) := by
  cases h with
  | EListIndex _ _ hl hi => exact ⟨_, _, hl, hi, rfl⟩

/-- A length inverted: the list its operand produced, and how many elements it had.  The cast to the
`Int` a `Value.int` holds is the rule's own, so what this hands back is the `Nat` the list has and
the equation it stands in. -/
public theorem Eval.listLength_inv {td : TypeDecls} {env : Env} {e : Expression} {v : Value}
    (h : Eval td env (.listLength e) v) :
    ∃ vs, Eval td env e (.list vs) ∧ v = .int (vs.length : Int) := by
  cases h with
  | EListLength _ he => exact ⟨_, he, rfl⟩

public theorem Eval.listMap_inv {td : TypeDecls} {env : Env} {e f : Expression} {v : Value}
    (h : Eval td env (.listMap e f) v) :
    ∃ vs vs' cb cg ps body, Eval td env e (.list vs) ∧ Eval td env f (.closure cb cg ps body) ∧
      vs.length = vs'.length ∧
      (∀ p ∈ vs.zip vs', Eval td (Env.extend ⟨cb, cg⟩ ps [p.1]) body p.2) ∧ v = .list vs' := by
  cases h with
  | EListMap _ _ he hf hlen _ hev => exact ⟨_, _, _, _, _, _, he, hf, hlen, hev, rfl⟩

public theorem Eval.listFlatMap_inv {td : TypeDecls} {env : Env} {e f : Expression} {v : Value}
    (h : Eval td env (.listFlatMap e f) v) :
    ∃ vs vss cb cg ps body, Eval td env e (.list vs) ∧ Eval td env f (.closure cb cg ps body) ∧
      vs.length = vss.length ∧
      (∀ p ∈ vs.zip vss, Eval td (Env.extend ⟨cb, cg⟩ ps [p.1]) body (.list p.2)) ∧
      v = .list vss.flatten := by
  cases h with
  | EListFlatMap _ _ he hf hlen _ hev => exact ⟨_, _, _, _, _, _, he, hf, hlen, hev, rfl⟩

/-- The keys are what the sort's order is read off, so they are what this hands back beside the
elements: the value is the elements paired with their keys and reordered, which is the rule's own
`Value.sortByKey`.

The comparability premise is dropped with the `ArgsHaveType` ones.  It is what makes a sort whose
keys cannot all be compared stuck, and the order the value carries is `Value.sortByKey`'s whether or
not a proof has it to hand. -/
public theorem Eval.listSortOn_inv {td : TypeDecls} {env : Env} {e f : Expression} {v : Value}
    (h : Eval td env (.listSortOn e f) v) :
    ∃ vs ks cb cg ps body, Eval td env e (.list vs) ∧ Eval td env f (.closure cb cg ps body) ∧
      vs.length = ks.length ∧
      (∀ p ∈ vs.zip ks, Eval td (Env.extend ⟨cb, cg⟩ ps [p.1]) body p.2) ∧
      v = .list ((Value.sortByKey (vs.zip ks)).map Prod.fst) := by
  cases h with
  | EListSortOn _ _ he hf hlen _ hev _ => exact ⟨_, _, _, _, _, _, he, hf, hlen, hev, rfl⟩

/-- Sorting by a comparison rearranges and nothing else, which is all this says: the `cmp` the rule
holds to the DSL function is existential here, so what is left is that the value is *some* stable
sort of the elements — enough for every fact about which elements it holds, and for nothing about
the order they are in.  A proof that needs the order has to `cases` the evaluation and work from the
comparison's own answers. -/
public theorem Eval.listSortBy_inv {td : TypeDecls} {env : Env} {e f : Expression} {v : Value}
    (h : Eval td env (.listSortBy e f) v) :
    ∃ vs cmp, Eval td env e (.list vs) ∧ v = .list (Value.sortWith cmp vs) := by
  cases h with
  | EListSortBy _ _ he _ _ _ => exact ⟨_, _, he, rfl⟩

/-- A search inverted is its two rules read as the two shapes its value can have: an index, with
every element before it one the predicate turned down and the element at it the one it accepted, or
the empty option with every element turned down.

Which disjunct holds is settled by the value rather than by anything a proof has to choose — an
`.option (some ...)` is the first rule's and an `.option none` the second's, since neither rule
produces the other's shape.  So a proof that knows what the search answered has one case to make.

`post` is existential and nothing is said about it: the elements after the match were never handed to
the predicate, which is the short circuit the rule carries and the one thing this inversion cannot
hand back.

`ArgsHaveType` premises are dropped as they are everywhere here. -/
public theorem Eval.listFindIndex_inv {td : TypeDecls} {env : Env} {e f : Expression} {v : Value}
    (h : Eval td env (.listFindIndex e f) v) :
    ∃ vs cb cg ps body, Eval td env e (.list vs) ∧ Eval td env f (.closure cb cg ps body) ∧
      ((∃ pre w post,
            vs = pre ++ w :: post ∧
              (∀ u ∈ pre, Eval td (Env.extend ⟨cb, cg⟩ ps [u]) body (.bool false)) ∧
                Eval td (Env.extend ⟨cb, cg⟩ ps [w]) body (.bool true) ∧
                  v = .option (some (.int (pre.length : Int)))) ∨
        (∀ u ∈ vs, Eval td (Env.extend ⟨cb, cg⟩ ps [u]) body (.bool false)) ∧ v = .option none) := by
  cases h with
  | EListFindIndexSome _ _ he hf _ hpre _ hw =>
    exact ⟨_, _, _, _, _, he, hf, .inl ⟨_, _, _, rfl, hpre, hw, rfl⟩⟩
  | EListFindIndexNone _ _ he hf _ hall => exact ⟨_, _, _, _, _, he, hf, .inr ⟨hall, rfl⟩⟩

/-! ### The shapes a form gives

And where no type is to hand: a form whose every rule builds a value of one shape produces one,
whatever its operands did.  These are the two such forms a mismatch rule one step out asks about —
a get, whose option is what `optionMatch` matches on, and an ordering, whose `bool` is what a sort
holds its comparison to — read off the rule rather than off a declaration's result type. -/

public theorem Eval.isOption_hashmapGet {td : TypeDecls} {env : Env} {m k : Expression} {v : Value}
    (h : Eval td env (.hashmapGet m k) v) : v.IsOption := by
  cases h with
  | EHashmapGet _ _ _ _ _ => exact ⟨_, rfl⟩

public theorem Eval.isBool_le {td : TypeDecls} {env : Env} {l r : Expression} {v : Value}
    (h : Eval td env (.le l r) v) : v.IsBool := by
  cases h with
  | ELe _ _ _ _ _ => exact ⟨_, rfl⟩

public theorem Eval.isBool_equals {td : TypeDecls} {env : Env} {l r : Expression} {v : Value}
    (h : Eval td env (.equals l r) v) : v.IsBool := by
  cases h with
  | EEquals _ _ _ _ _ => exact ⟨_, rfl⟩

/-- An index and a search both produce options, the one because a position the list has nothing at
is an answer like any other and the other because a list the predicate accepts nothing in is: in
both cases the `none` is a value rather than a failure, which is why both rules build an option
whatever happened underneath. -/
public theorem Eval.isOption_listIndex {td : TypeDecls} {env : Env} {l i : Expression} {v : Value}
    (h : Eval td env (.listIndex l i) v) : v.IsOption := by
  cases h with
  | EListIndex _ _ _ _ => exact ⟨_, rfl⟩

public theorem Eval.isOption_listFindIndex {td : TypeDecls} {env : Env} {e f : Expression}
    {v : Value} (h : Eval td env (.listFindIndex e f) v) : v.IsOption := by
  cases h with
  | EListFindIndexSome _ _ _ _ _ _ _ _ => exact ⟨_, rfl⟩
  | EListFindIndexNone _ _ _ _ _ _ => exact ⟨_, rfl⟩


/-- Evaluating a well-typed expression produces a value of its inferred type.

`Expression.unreachable` costs this nothing, for the reason it has no rule: the induction is over
`Eval`, so a form with no rule contributes no case, and its annotation is never compared against a
value because there is never a value. -/
public theorem Eval.hasType {td : TypeDecls} {env : Env} {ctx : Context} {e : Expression}
    {v : Value} {t : Ty} (h : Eval td env e v) (henv : Env.HasType td env ctx)
    (ht : e.infer td (ctx ++ Globals.types env.globals) = some t) : v.HasType td t := by
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
        | some t' =>
          obtain ⟨v', hv', -⟩ := hval x t' hc; simp [hv'] at hb
      rw [Env.lookup_of_globals hb] at hx
      rw [hcn, Globals.lookup_types] at ht
      obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp ht
      rw [hd, Option.map_some] at hx
      obtain rfl : v = Globals.value env.globals d := (Option.some.inj hx).symm
      refine Value.hasType_closure_iff.mpr ⟨[], d.resultType, ?_, ?_, ?_⟩
      · exact Globals.hasType_env hgs
      · simpa using FuncDecl.wellTyped_iff_infer_eq_some.mp (hgs x d hd)
      · simp [FuncDecl.ty]
  | ECons e₁ e₂ h₁ h₂ ih₁
    ih₂ =>
    obtain ⟨t', ht₁, ht₂, rfl⟩ := Expression.infer_lcons_eq_some.mp ht
    have hv := ih₁ henv ht₁
    cases ih₂ henv ht₂ with
    | list hall => exact .list (by grind)
  | ELam ps body =>
    obtain ⟨r, hbody, rfl⟩ := Expression.infer_lam_eq_some.mp ht
    exact Value.hasType_closure_iff.mpr ⟨ctx, r, henv, by simpa using hbody, rfl⟩
  | EApp f args hf _ _ hat hbody ihf _
    ihbody =>
    obtain ⟨ps', hfty, _⟩ := Expression.infer_app_eq_some.mp ht
    obtain ⟨cctx, r, hcenv, hbodyty, heq⟩ := Value.hasType_closure_iff.mp (ihf henv hfty)
    injection heq with _ hr
    refine ihbody (Env.hasType_extend hat hcenv) ?_
    simp only [Env.globals_extend]
    exact hr ▸ hbodyty
  | EIteTrue c thn els _ _ _
    ihthn =>
    obtain ⟨-, hthn, -⟩ := Expression.infer_ite_eq_some.mp ht
    exact ihthn henv hthn
  | EIteFalse c thn els _ _ _
    ihels =>
    obtain ⟨-, -, hels⟩ := Expression.infer_ite_eq_some.mp ht
    exact ihels henv hels
  | ELet x e body _ _ ih₁
    ihbody =>
    obtain ⟨t', ht', htbody⟩ := Expression.infer_let_eq_some.mp ht
    exact ihbody (Env.hasType_cons (ih₁ henv ht') henv) htbody
  | EStructNew name fes hnames hev
    ihev =>
    obtain ⟨sd, fts, hsd, hfts, hcomplete, rfl⟩ := Expression.infer_structNew_eq_some.mp ht
    -- Three lists with one set of names between them: the declaration's fields, the types
    -- inference gave the expressions, and the values those evaluated to.  The last two are in the
    -- order the fields were written and the first need not be, so the declaration is reached
    -- through `fieldsComplete` and the other two through the keys they share.
    have hkeys : fts.map Prod.fst = fes.map Prod.fst := Expression.map_fst_of_inferFields hfts
    have hdom : ∀ f, (sd.fields.lookup f).isSome = (fes.lookup f).isSome := fun f =>
      (Expression.lookup_isSome_of_fieldsComplete hcomplete f).trans
        (List.lookup_isSome_congr hkeys f)
    -- The names clause is `fieldsComplete`'s own permutation, carried along the two equalities: a
    -- field written twice is what it turns down, and that is what the clause now asks of the value.
    refine
      .struct hsd
        (by
          rw [← hnames, ← hkeys]
          exact (Expression.fieldsComplete_eq_true.mp hcomplete).1)
        fun f t' v' hft hfv => ?_
    obtain ⟨e, he⟩ : ∃ e, fes.lookup f = some e :=
      Option.isSome_iff_exists.mp
        (by
          rw [← hdom f]; simp [hft])
    obtain ⟨t'', hft'', hinfer⟩ := Expression.lookup_of_inferFields hfts he
    obtain rfl : t'' = t' := by
      have := (Expression.fieldsComplete_eq_true.mp hcomplete).2 (f, t'') (List.mem_of_lookup hft'')
      grind
    exact ihev _ (List.mem_zip_of_lookup hnames he hfv) henv hinfer
  | EStructGet e f _ hfv
    ihe =>
    obtain ⟨name', sd, he, hsd, hft⟩ := Expression.infer_structGet_eq_some.mp ht
    obtain ⟨sd', hsd', -, htys, hname⟩ := Value.hasType_struct_iff.mp (ihe henv he)
    simp only [Ty.struct.injEq] at hname
    subst hname
    obtain rfl : sd' = sd := by grind
    exact htys _ _ _ hft hfv
  | EStructUpdate e fes _ hnames hev ihe
    ihev =>
    obtain ⟨name', sd, fts, he, hsd, hfts, -, hfields, rfl⟩ :=
      Expression.infer_structUpdate_eq_some.mp ht
    obtain ⟨sd', hsd', hperm, htys, hname⟩ := Value.hasType_struct_iff.mp (ihe henv he)
    simp only [Ty.struct.injEq] at hname
    subst hname
    obtain rfl : sd' = sd := by grind
    -- An update rebinds in place, so the names it hands back are the ones the operand's own clause
    -- already placed against the declaration's.
    refine
      .struct hsd (by simpa using hperm) fun f t' v' hft hfv =>
        FieldValues.hasType_update htys ?_ hft hfv
    -- What is left is the *new* values: each one is a field's expression evaluated, and the type
    -- checker has already said that expression has the type the declaration gives that field.
    intro f t' v' hft hus
    obtain ⟨e', he'⟩ : ∃ e', fes.lookup f = some e' :=
      Option.isSome_iff_exists.mp
        (by
          rw [List.lookup_isSome_congr hnames f]; simp [hus])
    obtain ⟨t'', hft'', hinfer⟩ := Expression.lookup_of_inferFields hfts he'
    obtain rfl : t'' = t' := by
      have := hfields (f, t'') (List.mem_of_lookup hft'')
      grind
    exact ihev _ (List.mem_zip_of_lookup hnames he' hus) henv hinfer
  | EIndNew name c args hlen hev
    ihev =>
    obtain ⟨d, ts, hd, hc, hts, rfl⟩ := Expression.infer_indNew_eq_some.mp ht
    obtain ⟨hvlen, hall⟩ :=
      Value.hasType_zip_of_inferList hlen hts fun p hp t' ht' => ihev p hp henv ht'
    exact .ind hd hc hvlen hall
  | EIndMatch scrut alts _ halt _ ihscrut
    ihbody =>
    obtain ⟨name', d, rs, hsc, hd, -, halts, -, hrs⟩ := Expression.infer_indMatch_eq_some.mp ht
    obtain ⟨d', ts, hd', hc, hvlen, hvals, hname⟩ := Value.hasType_ind_iff.mp (ihscrut henv hsc)
    simp only [Ty.ind.injEq] at hname
    subst hname
    obtain rfl : d' = d := by grind
    -- The alternative the value's constructor resolves to is the one checked against that
    -- constructor's data types, and every alternative was checked at the match's own type.
    obtain ⟨t', htmem, hxlen, hinfer⟩ := Expression.lookup_of_inferAlts halts hc halt
    obtain rfl : t' = t := hrs t' htmem
    exact ihbody (Env.hasType_match hxlen hvlen hvals henv) (by simpa using hinfer)
  | EOptionMatchNone scrut nbody x sbody _ _ _
    ihnbody =>
    obtain ⟨-, -, hnb, -⟩ := Expression.infer_optionMatch_eq_some.mp ht
    exact ihnbody henv hnb
  | EOptionMatchSome scrut nbody x sbody _ _ ihscrut
    ihsbody =>
    obtain ⟨t', hsc, -, hsb⟩ := Expression.infer_optionMatch_eq_some.mp ht
    -- The type of the name this case binds is the one the scrutinee's option type holds, which is
    -- the only thing the value it took apart says about what it carries.
    obtain ⟨t'', hw, heq⟩ := Value.hasType_option_some_iff.mp (ihscrut henv hsc)
    obtain rfl : t'' = t' := by simpa using heq.symm
    exact ihsbody (Env.hasType_cons hw henv) (by simpa using hsb)
  | EListMatchNil scrut nbody hd tl cbody _ _ _
    ihnbody =>
    obtain ⟨-, -, hnb, -⟩ := Expression.infer_listMatch_eq_some.mp ht
    exact ihnbody henv hnb
  | EListMatchCons scrut nbody hd tl cbody _ _ ihscrut
    ihcbody =>
    obtain ⟨t', hsc, -, hcb⟩ := Expression.infer_listMatch_eq_some.mp ht
    -- The two names this case binds stand at the element type the scrutinee's list type gives and at
    -- that list type itself, and the value it took apart is a list of elements of the first: the head
    -- is one of them and the tail is the rest, which is a list of them again.
    cases ihscrut henv hsc with
    | list hall =>
      exact
        ihcbody
          (Env.hasType_cons (hall _ (List.mem_cons_self ..))
            (Env.hasType_cons (.list fun u hu => hall u (List.mem_cons_of_mem _ hu)) henv))
          (by simpa using hcb)
  | EListIndex l i _ _ ihl
    _ =>
    obtain ⟨t', hl, -, rfl⟩ := Expression.infer_listIndex_eq_some.mp ht
    -- Which position produced the element does not matter: a list is homogeneous, so having found
    -- one at all is what types the result, exactly as having found a binding types a get.
    cases ihl henv hl with
    | list hall =>
      cases hidx : Value.index? _ _ with
      | none => exact .optionNone
      | some w => exact .optionSome (hall w (Value.mem_of_index? hidx))
  | @EListMap _ _ _ _ _ _ vs' e f _ _ hlen hat _ _ ihf
    ihev =>
    obtain ⟨t', r, -, hf, rfl⟩ := Expression.infer_listMap_eq_some.mp ht
    -- The function is a closure whose body was checked against a context of its own, exactly as in
    -- `EApp`, so what each call produced is of the closure's result type — which is the element
    -- type of the list the mapping built.  The list it was given contributes nothing: its element
    -- type is the function's parameter type and goes no further, so this is the one mapping rule
    -- that needs no induction hypothesis for its first operand.
    obtain ⟨cctx, r', hcenv, hbodyty, heqf⟩ := Value.hasType_closure_iff.mp (ihf henv hf)
    injection heqf with _ hr
    subst hr
    exact
      .list
        (Value.hasType_listMap hlen fun p hp =>
          ihev p hp (Env.hasType_extend (hat p hp) hcenv) (by simpa using hbodyty))
  | @EListFlatMap _ _ _ _ _ _ vss e f _ _ hlen hat _ _ ihf
    ihev =>
    obtain ⟨t', r, -, hf, rfl⟩ := Expression.infer_listFlatMap_eq_some.mp ht
    -- `EListMap`'s case with one more step: the closure's result type is a *list* type here, so what
    -- each call produced is a list of the elements the flattening hands back, and taking that list's
    -- own `Value.HasType` apart is what gets down to them.  The list the form was given contributes
    -- nothing, exactly as it contributes nothing there.
    obtain ⟨cctx, r', hcenv, hbodyty, heqf⟩ := Value.hasType_closure_iff.mp (ihf henv hf)
    injection heqf with _ hr
    subst hr
    refine .list (Value.hasType_listFlatMap hlen fun p hp => ?_)
    cases ihev p hp (Env.hasType_extend (hat p hp) hcenv) (by simpa using hbodyty) with
    | list hall => exact hall
  | EListSortOn e f _ _ _ _ _ _ ihl _
    _ =>
    obtain ⟨t', r, hl, -, -, rfl⟩ := Expression.infer_listSortOn_eq_some.mp ht
    -- The projection contributes nothing to the type: its calls produced the keys, and those are
    -- dropped once the order is settled.  So this is the one mapping-shaped rule proved from the
    -- induction hypothesis for its *first* operand, which is where `EListMap` needs none.
    cases ihl henv hl with
    | list hall => exact .list (Value.hasType_sortByKey hall)
  | EListSortBy e f _ _ _ _ ihl _
    _ =>
    obtain ⟨t', hl, -, rfl⟩ := Expression.infer_listSortBy_eq_some.mp ht
    -- The comparison contributes nothing to the type either, and here there is not even a key for
    -- it to have produced: its answers settled the order and are `bool`s whatever the elements were.
    cases ihl henv hl with
    | list hall => exact .list (Value.hasType_sortWith hall)
  | EHashmapPut m k v _ _ _ herase ihm ihk
    ihv =>
    obtain ⟨kt, vt, hm, hk, hv, -, rfl⟩ := Expression.infer_hashmapPut_eq_some.mp ht
    obtain ⟨kt', vt', hkeys, hvals, heq⟩ := Value.hasType_hashmap_iff.mp (ihm henv hm)
    obtain ⟨rfl, rfl⟩ : kt = kt' ∧ vt = vt' := by simpa using heq
    -- The new binding is typed by the induction hypotheses for the key and the value expressions;
    -- every other binding is one the map already carried, so the map's own type speaks for it.
    refine .hashmap (fun p hp => ?_) (fun p hp => ?_) <;> rcases List.mem_cons.mp hp with rfl | hp'
    · simpa using ihk henv hk
    · exact hkeys p (KeyValues.mem_of_erase? herase hp')
    · simpa using ihv henv hv
    · exact hvals p (KeyValues.mem_of_erase? herase hp')
  | @EHashmapGet _ _ _ o m k _ _ hlookup ihm
    ihk =>
    obtain ⟨kt, vt, hm, hk, -, rfl⟩ := Expression.infer_hashmapGet_eq_some.mp ht
    obtain ⟨kt', vt', -, hvals, heq⟩ := Value.hasType_hashmap_iff.mp (ihm henv hm)
    obtain ⟨rfl, rfl⟩ : kt = kt' ∧ vt = vt' := by simpa using heq
    -- Which key produced the value does not matter: every value a hashmap carries is at the one
    -- type its hashmap type gives, so having found a binding at all is what types the result.
    cases o with
    | none => exact .optionNone
    | some w =>
      obtain ⟨k', hk'⟩ := KeyValues.mem_of_lookup? hlookup
      exact .optionSome (hvals (k', w) hk')
  | @EHashmapMap _ _ _ _ _ _ kvs' m f _ _ hkeys hat _ ihm ihf
    ihev =>
    obtain ⟨kt, vt, r, hm, hf, -, rfl⟩ := Expression.infer_hashmapMap_eq_some.mp ht
    obtain ⟨kt', vt', hkeystys, -, heq⟩ := Value.hasType_hashmap_iff.mp (ihm henv hm)
    obtain ⟨rfl, rfl⟩ : kt = kt' ∧ vt = vt' := by simpa using heq
    -- The function is a closure whose body was checked against a context of its own, exactly as in
    -- `EApp`, so what each call produced is of the closure's result type — which is the value half
    -- of the map the mapping built.
    obtain ⟨cctx, r', hcenv, hbodyty, heqf⟩ := Value.hasType_closure_iff.mp (ihf henv hf)
    injection heqf with _ hr
    subst hr
    obtain ⟨hkeys', hvals'⟩ :
      (∀ p ∈ kvs', Value.HasType td p.1 kt) ∧ ∀ p ∈ kvs', Value.HasType td p.2 r :=
      KeyValues.hasType_map hkeys hkeystys fun p hp =>
        ihev p hp (Env.hasType_extend (hat p hp) hcenv) (by simpa using hbodyty)
    exact .hashmap hkeys' hvals'
  | EHashmapToList m _
    ihm =>
    obtain ⟨kt, vt, hm, -, rfl⟩ := Expression.infer_hashmapToList_eq_some.mp ht
    obtain ⟨kt', vt', hkeys, hvals, heq⟩ := Value.hasType_hashmap_iff.mp (ihm henv hm)
    obtain ⟨rfl, rfl⟩ : kt = kt' ∧ vt = vt' := by simpa using heq
    -- Every element is a binding of the map, so the two halves of the map's own type are what
    -- type the two positions of the tuple it became.
    refine .list fun v hv => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
    refine .tuple (by simp) fun q hq => ?_
    rcases (by simpa using hq : q = (p.1, kt) ∨ q = (p.2, vt)) with rfl | rfl
    · exact hkeys p hp
    · exact hvals p hp
  | ETupleNew es hlen hev
    ihev =>
    obtain ⟨ts, hts, rfl⟩ := Expression.infer_tupleNew_eq_some.mp ht
    obtain ⟨hvlen, hall⟩ :=
      Value.hasType_zip_of_inferList hlen hts fun p hp t' ht' => ihev p hp henv ht'
    exact .tuple hvlen hall
  | ETupleGet e i _ hget
    ihe =>
    obtain ⟨ts, he, hi⟩ := Expression.infer_tupleGet_eq_some.mp ht
    obtain ⟨ts', -, htys, heq⟩ := Value.hasType_tuple_iff.mp (ihe henv he)
    obtain rfl : ts = ts' := by simpa using heq
    -- The value and the type are two lists of the same length, so the value at the index and the
    -- type at it are a pair the tuple's own `Value.HasType` already speaks for.
    exact htys _ (List.mem_zip_of_getElem? hget hi)
  | _ => grind [Value.HasType]

/-- `Apply d gs args v`: calling `d` with `args` among the globals `gs` returns `v`.

A call binds the parameters to the arguments positionally and evaluates the body under those
bindings over `gs`, so a body mentioning a name that is neither a parameter nor a global has no
value.

The `ArgsHaveType` premise is what makes a call with the wrong arguments stuck rather than junk:
arguments of the wrong type, or the wrong number of them, produce no value at all.  It is also
all `Apply.hasType` needs to read `d.parameters` as the context the body was checked in. -/
public inductive FuncDecl.Apply (d : FuncDecl) (td : TypeDecls) (gs : Globals) :
    List Value → Value → Prop where
  |
  EApply (args : List Value) :
    ArgsHaveType td d.parameters args → Eval td (d.callEnv gs args) d.body v → Apply d td gs args v

/-- Calling a well-typed declaration among well-typed globals returns a value of its declared result
type.

Unlike `Eval.hasType` this needs no hypothesis about the local environment: `Apply` already requires
the arguments to match the parameters, and `Env.hasType_callEnv` turns that into the agreement
between environment and context that `Eval.hasType` asks for.  What is left is a property of the
declaration and the globals alone — nothing about this particular call. -/
public theorem FuncDecl.Apply.hasType {d : FuncDecl} {td : TypeDecls} {gs : Globals}
    {args : List Value} {v : Value} (h : d.Apply td gs args v) (hgs : Globals.WellTyped td gs)
    (hd : d.WellTyped td gs) : v.HasType td d.resultType := by
  cases h with
  | EApply _ hargs hbody =>
    exact hbody.hasType (Env.hasType_callEnv hgs hargs) (by simpa [FuncDecl.callEnv] using hd)

/-- A body calls another declaration by mentioning its name, and this is that step inverted: an
`app` whose function is a `varRef` the local bindings do not shadow is a call to whatever the globals
table declares under that name.

The two hypotheses are what `Env.lookup` consults, in the order it consults them: `hb` says the name
is not shadowed by a local binding — a parameter or a `let` of that name would be the value called
instead — and `hd` says what the table has under it.  Neither is about this call, so both are
discharged once per name by `simp` over the environment a body runs in.

This is the one inversion principle that produces a `FuncDecl.Apply` rather than an `Eval`, which is
what makes a proof about a declaration that calls others a proof built out of theorems about those
others rather than one that unfolds them. -/
public theorem FuncDecl.apply_of_eval_app {td : TypeDecls} {env : Env} {x : String} {d : FuncDecl}
    {args : List Expression} {v : Value} (hd : env.globals.lookup x = some d)
    (hb : env.bindings.lookup x = none) (h : Eval td env (.app (.varRef x) args) v) :
    ∃ vs, args.length = vs.length ∧ (∀ p ∈ args.zip vs, Eval td env p.1 p.2) ∧
      d.Apply td env.globals vs v := by
  cases h with
  | EApp f as hf hlen hargs hat hbody =>
    have hx := Eval.varRef_inv hf
    rw [Env.lookup_of_globals hb, hd, Option.map_some, Option.some.injEq] at hx
    simp only [Globals.value, Globals.env, Env.closure, Value.closure.injEq] at hx
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hx
    exact ⟨_, hlen, hargs, .EApply _ hat (by simpa [FuncDecl.callEnv, Globals.env] using hbody)⟩

/-- The converse of `FuncDecl.apply_of_eval_app`: a `FuncDecl.Apply` of `d` is an `Eval` of a call
to whatever name the globals table holds `d` under, provided that name is not shadowed locally.

Where that lemma takes a derivation about a call apart, this builds one: a proof that calls another
declaration — stated as an `Apply` of it, which is what every theorem about a declaration concludes
— is turned into the `Eval` of the `app` that invokes it, which is what a *caller's* body actually
contains.  This is the step that makes a forward proof about a declaration calling another into a
forward proof about the caller, the way `FuncDecl.apply_of_eval_app` makes a backward one. -/
public theorem FuncDecl.eval_app_of_apply {td : TypeDecls} {env : Env} {x : String} {d : FuncDecl}
    {args : List Expression} {vs : List Value} {v : Value} (hd : env.globals.lookup x = some d)
    (hb : env.bindings.lookup x = none) (hlen : args.length = vs.length)
    (hargs : ∀ p ∈ args.zip vs, Eval td env p.1 p.2) (h : d.Apply td env.globals vs v) :
    Eval td env (.app (.varRef x) args) v := by
  cases h with
  | EApply _ hat hbody =>
    refine Eval.EApp _ _ (Eval.EVarRef _ ?_) hlen hargs hat
      (by simpa [FuncDecl.callEnv, Globals.env] using hbody)
    rw [Env.lookup_of_globals hb, hd, Option.map_some]
    simp [Globals.value, Globals.env, Env.closure]

/-- Every declaration in a well-typed globals table is well typed, so a call to any of them returns
a value of the type it declares. -/
public theorem Globals.apply_hasType {td : TypeDecls} {gs : Globals} {x : String} {d : FuncDecl}
    {args : List Value} {v : Value} (hgs : Globals.WellTyped td gs) (hx : gs.lookup x = some d)
    (h : d.Apply td gs args v) : v.HasType td d.resultType :=
  h.hasType hgs (hgs x d hx)

/-- `p.Apply x args v`: calling the declaration `p` gives the name `x` with `args` returns `v`.

The body runs among `p`'s own globals and its own structure types, so it may call anything else `p`
declares — itself included — and mention any struct it declares.  A name `p` does not declare has no
call at all, which is the only way this differs from `FuncDecl.Apply` on `p.globals`. -/
public inductive Program.Apply (p : Program) (x : String) : List Value → Value → Prop where
  |
  call (d : FuncDecl) :
    p.lookup x = some d → d.Apply p.typeDecls p.globals args v → Apply p x args v

/-- Calling a name in a well-typed program returns a value of the type the declaration under that
name declares.

This is the top of the stack: `Program.WellTyped` is a property of the program alone, checked once
by `Program.check`, and it covers every call to every name in it. -/
public theorem Program.Apply.hasType {p : Program} {x : String} {d : FuncDecl} {args : List Value}
    {v : Value} (h : p.Apply x args v) (hp : p.WellTyped) (hx : p.lookup x = some d) :
    v.HasType p.typeDecls d.resultType := by
  cases h with
  | call d' hx' hbody =>
    obtain rfl : d' = d := by grind
    exact Globals.apply_hasType hp hx' hbody
