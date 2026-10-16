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
| ELam (ps : List (String × Ty)) (body : Expression) :
    Eval td env (.lam ps body) (env.closure ps body)
/-- A call evaluates its function and its arguments, then the body in the closure's environment
extended with the parameters. -/
| EApp (f : Expression) (args : List Expression) :
    Eval td env f (.closure cbindings cglobals ps body) →
    args.length = vs.length → (∀ p ∈ args.zip vs, Eval td env p.1 p.2) →
    ArgsHaveType td ps vs →
    Eval td (Env.extend ⟨cbindings, cglobals⟩ ps vs) body v →
    Eval td env (.app f args) v
| EBoolLit (b : Bool) : Eval td env (.boolLit b) (.bool b)
/-- A conditional whose condition came out `true` evaluates its first branch, and one whose condition
came out `false` its second.

Two rules rather than one over a `Bool`, so that a proof taking an `ite` apart is left with the branch
that ran rather than with an `if` to reduce, and so that the branch not taken is not mentioned at all:
it is never evaluated, which is the whole of what a conditional does that a two-argument function
could not.

A condition that evaluates to anything but a `bool` leaves this stuck — the only thing that can go
wrong here, and exactly what typing rules out. -/
| EIteTrue (c thn els : Expression) :
    Eval td env c (.bool true) → Eval td env thn v →
    Eval td env (.ite c thn els) v
| EIteFalse (c thn els : Expression) :
    Eval td env c (.bool false) → Eval td env els v →
    Eval td env (.ite c thn els) v
| EBoolAndFalse (l r : Expression) :
    Eval td env l (.bool false) →
    Eval td env (.boolAnd l r) (.bool false)
| EBoolAndTrue (l r : Expression) :
    Eval td env l (.bool true) → Eval td env r (.bool b) →
    Eval td env (.boolAnd l r) (.bool b)
| EBoolOrTrue (l r : Expression) :
    Eval td env l (.bool true) →
    Eval td env (.boolOr l r) (.bool true)
| EBoolOrFalse (l r : Expression) :
    Eval td env l (.bool false) → Eval td env r (.bool b) →
    Eval td env (.boolOr l r) (.bool b)
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
`Value.eq_of_beq?` and `Value.ne_of_beq?` turn into Lean's own equality. -/
| EEquals (l r : Expression) :
    Eval td env l v₁ → Eval td env r v₂ → Value.beq? v₁ v₂ = some b →
    Eval td env (.equals l r) (.bool b)
/-- Let binds a variable that shadows any existing bindings.

    The bound value is available in the body of the let.  This is a non-recursive let. -/
| ELet (x : String) (e : Expression) (body : Expression) :
    Eval td env e v₁ →
    Eval td ⟨(x, v₁) :: env.bindings, env.globals⟩ body v →
    Eval td env (.let_ x e body) v
| EVarRef (x : String) : env.lookup x = some v → Eval td env (.varRef x) v
/-- Building a struct evaluates each field's expression and keeps the result under that field's name.

The fields come out under the names they went in under and in the order they went in, which is what
`fes.map Prod.fst = fvs.map Prod.fst` says; the premise over the zip is then one evaluation per
field, the way `EApp`'s is one per argument.  Which names those are is not checked here — the
declaration is not consulted — so a `structNew` naming fields the struct does not have still
evaluates.  Being ill typed is what rules it out. -/
| EStructNew (name : String) (fes : List (FieldName × Expression)) :
    fes.map Prod.fst = fvs.map Prod.fst →
    (∀ p ∈ fes.zip fvs, Eval td env p.1.2 p.2.2) →
    Eval td env (.structNew name fes) (.struct name fvs)
/-- Reading a field evaluates the struct and hands back what that field is bound to.

Bound in the *value*, not declared in the struct: a field the value does not carry leaves this stuck,
which is the only thing that can go wrong here and is exactly what typing rules out. -/
| EStructGet (e : Expression) (f : FieldName) :
    Eval td env e (.struct name fvs) → fvs.lookup f = some v →
    Eval td env (.structGet e f) v
/-- Updating a struct evaluates it, evaluates each new field value, and rebinds those fields.

`FieldValues.update` rebinds in place, so the result carries the same fields in the same order as the
struct it came from and differs only in what the named ones hold.  Fields the update names that the
struct does not have are therefore dropped rather than added — again a case typing rules out. -/
| EStructUpdate (e : Expression) (fes : List (FieldName × Expression)) :
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
| EIndNew (name : String) (c : CtorName) (args : List Expression) :
    args.length = vs.length → (∀ p ∈ args.zip vs, Eval td env p.1 p.2) →
    Eval td env (.indNew name c args) (.ind name c vs)
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
| EIndMatch (scrut : Expression) (alts : List (CtorName × List String × Expression)) :
    Eval td env scrut (.ind name c vs) →
    alts.lookup c = some (xs, body) →
    Eval td ⟨xs.zip vs ++ env.bindings, env.globals⟩ body v →
    Eval td env (.indMatch scrut alts) v
| EIntLit (i : Int) : Eval td env (.intLit i) (.int i)
| EPlus (e₁ : Expression) (e₂ : Expression) : Eval td env e₁ (.int n₁) → Eval td env e₂ (.int n₂) → Eval td env (.plus e₁ e₂) (.int (n₁ + n₂))
| EMinus (e₁ : Expression) (e₂ : Expression) : Eval td env e₁ (.int n₁) → Eval td env e₂ (.int n₂) → Eval td env (.minus e₁ e₂) (.int (n₁ - n₂))
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
| EOptionMatchNone (scrut nbody : Expression) (x : String) (sbody : Expression) :
    Eval td env scrut (.option none) →
    Eval td env nbody v →
    Eval td env (.optionMatch scrut nbody x sbody) v
| EOptionMatchSome (scrut nbody : Expression) (x : String) (sbody : Expression) :
    Eval td env scrut (.option (some w)) →
    Eval td ⟨(x, w) :: env.bindings, env.globals⟩ sbody v →
    Eval td env (.optionMatch scrut nbody x sbody) v
| ENil (ty : Ty) : Eval td env (.lnil ty) (.list [])
| ECons (e₁ : Expression) (e₂ : Expression) : Eval td env e₁ v → Eval td env e₂ (.list vs) → Eval td env (.lcons e₁ e₂) (.list (v :: vs))
/-- Map `f` over `e` (of type List α).

The length equality clause is a guarantee that the result list is always
the same length as the input. -/
| EListMap (e f : Expression) :
    Eval td env e (.list vs) →
    Eval td env f (.closure cbindings cglobals ps body) →
    vs.length = vs'.length →
    (∀ p ∈ vs.zip vs', ArgsHaveType td ps [p.1]) →
    (∀ p ∈ vs.zip vs', Eval td (Env.extend ⟨cbindings, cglobals⟩ ps [p.1]) body p.2) →
    Eval td env (.listMap e f) (.list vs')
/-- A length evaluates the list and hands back how many elements it has, as an `int`.

`List.length` is a `Nat` and `Value.int` holds an `Int`, so the count is cast on the way out: the IR
has no natural number type, and a length is one of the few places a `Nat` would otherwise appear.
The cast is total and loses nothing — a length is never negative — which is why this needs no premise
beyond evaluating the operand.

The elements are not looked at, only counted, so unlike `EListReverse` this is a rule whose result
mentions none of them.  A non-list operand leaves it stuck, which is the only thing that can go
wrong here and is exactly what typing rules out. -/
| EListLength (e : Expression) :
    Eval td env e (.list vs) → Eval td env (.listLength e) (.int (vs.length : Int))
| EListReverse (e : Expression) : Eval td env e (.list vs) → Eval td env (.listReverse e) (.list vs.reverse)
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
| EHashmapPut (m k v : Expression) :
    Eval td env m (.hashmap kvs) → Eval td env k vk → Eval td env v vv →
    KeyValues.erase? kvs vk = some kvs' →
    Eval td env (.hashmapPut m k v) (.hashmap ((vk, vv) :: kvs'))
/-- A get evaluates the map and the key and hands back the option of what that key is bound to.

One rule rather than the two `optionMatch` has, and for the reason `EEquals` is one rule: what a
proof is left with here is not a choice between branches but the map, the key, and what
`KeyValues.lookup?` said about the two.  A key the map does not bind is not one of the things that
can go wrong — it is the empty option, which is a value like any other — and the `none` that leaves
this stuck is the one a put's does. -/
| EHashmapGet (m k : Expression) :
    Eval td env m (.hashmap kvs) → Eval td env k vk →
    KeyValues.lookup? kvs vk = some o →
    Eval td env (.hashmapGet m k) (.option o)
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
| EHashmapMap (m f : Expression) :
    Eval td env m (.hashmap kvs) →
    Eval td env f (.closure cbindings cglobals ps body) →
    kvs.map Prod.fst = kvs'.map Prod.fst →
    (∀ p ∈ kvs.zip kvs', ArgsHaveType td ps [p.1.1, p.1.2]) →
    (∀ p ∈ kvs.zip kvs', Eval td (Env.extend ⟨cbindings, cglobals⟩ ps [p.1.1, p.1.2]) body p.2.2) →
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
| EHashmapToList (m : Expression) :
    Eval td env m (.hashmap kvs) →
    Eval td env (.hashmapToList m) (.list (kvs.map fun p => .tuple [p.1, p.2]))
/-- Building a tuple evaluates one expression per element and keeps the values in the order they
were given, which is the order the type the expression is inferred at gives them.

The premise is one evaluation per element with the lengths pinned down separately, the way
`EIndNew`'s is one per argument and for the same reason: both are positional, and `List.zip` stops
at the shorter list.  Nothing here says how many elements there ought to be, which is the one way
this is easier than `EIndNew` — a constructor's arity is its declaration's, where a tuple's length
is read off the elements themselves. -/
| ETupleNew (es : List Expression) :
    es.length = vs.length → (∀ p ∈ es.zip vs, Eval td env p.1 p.2) →
    Eval td env (.tupleNew es) (.tuple vs)
/-- Reading an element evaluates the tuple and hands back the value at that position.

Read out of the *value*, as `EStructGet`'s field is: an index the value has nothing at leaves this
stuck, which is the only thing that can go wrong here and is exactly what typing rules out.  The
index is a `Nat` in the expression rather than something to evaluate, so there is no premise for it
— the position is settled before anything runs, which is what let `Expression.infer` read the type
at it. -/
| ETupleGet (e : Expression) (i : Nat) :
    Eval td env e (.tuple vs) → vs[i]? = some v →
    Eval td env (.tupleGet e i) v


/-- Evaluating a well-typed expression produces a value of its inferred type. -/
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
            | some t' => obtain ⟨v', hv', -⟩ := hval x t' hc; simp [hv'] at hb
          rw [Env.lookup_of_globals hb] at hx
          rw [hcn, Globals.lookup_types] at ht
          obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp ht
          rw [hd, Option.map_some] at hx
          obtain rfl : v = Globals.value env.globals d := (Option.some.inj hx).symm
          refine Value.hasType_closure_iff.mpr ⟨[], d.resultType, ?_, ?_, ?_⟩
          · exact Globals.hasType_env hgs
          · simpa using FuncDecl.wellTyped_iff_infer_eq_some.mp (hgs x d hd)
          · simp [FuncDecl.ty]
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
  | EIteTrue c thn els _ _ _ ihthn =>
      obtain ⟨-, hthn, -⟩ := Expression.infer_ite_eq_some.mp ht
      exact ihthn henv hthn
  | EIteFalse c thn els _ _ _ ihels =>
      obtain ⟨-, -, hels⟩ := Expression.infer_ite_eq_some.mp ht
      exact ihels henv hels
  | ELet x e body _ _ ih₁ ihbody =>
      obtain ⟨t', ht', htbody⟩ := Expression.infer_let_eq_some.mp ht
      exact ihbody (Env.hasType_cons (ih₁ henv ht') henv) htbody
  | EStructNew name fes hnames hev ihev =>
      obtain ⟨sd, fts, hsd, hfts, hcomplete, rfl⟩ := Expression.infer_structNew_eq_some.mp ht
      -- Three lists with one set of names between them: the declaration's fields, the types
      -- inference gave the expressions, and the values those evaluated to.  The last two are in the
      -- order the fields were written and the first need not be, so the declaration is reached
      -- through `fieldsComplete` and the other two through the keys they share.
      have hkeys : fts.map Prod.fst = fes.map Prod.fst := Expression.map_fst_of_inferFields hfts
      have hdom : ∀ f, (sd.fields.lookup f).isSome = (fes.lookup f).isSome := fun f =>
        (Expression.lookup_isSome_of_fieldsComplete hcomplete f).trans
          (List.lookup_isSome_congr hkeys f)
      refine .struct hsd (fun f => (hdom f).trans (List.lookup_isSome_congr hnames f))
        fun f t' v' hft hfv => ?_
      obtain ⟨e, he⟩ : ∃ e, fes.lookup f = some e :=
        Option.isSome_iff_exists.mp (by rw [← hdom f]; simp [hft])
      obtain ⟨t'', hft'', hinfer⟩ := Expression.lookup_of_inferFields hfts he
      obtain rfl : t'' = t' := by
        have := (Expression.fieldsComplete_eq_true.mp hcomplete).2 (f, t'')
          (List.mem_of_lookup hft'')
        grind
      exact ihev _ (List.mem_zip_of_lookup hnames he hfv) henv hinfer
  | EStructGet e f _ hfv ihe =>
      obtain ⟨name', sd, he, hsd, hft⟩ := Expression.infer_structGet_eq_some.mp ht
      obtain ⟨sd', hsd', -, htys, hname⟩ := Value.hasType_struct_iff.mp (ihe henv he)
      simp only [Ty.struct.injEq] at hname
      subst hname
      obtain rfl : sd' = sd := by grind
      exact htys _ _ _ hft hfv
  | EStructUpdate e fes _ hnames hev ihe ihev =>
      obtain ⟨name', sd, fts, he, hsd, hfts, -, hfields, rfl⟩ :=
        Expression.infer_structUpdate_eq_some.mp ht
      obtain ⟨sd', hsd', hdom, htys, hname⟩ := Value.hasType_struct_iff.mp (ihe henv he)
      simp only [Ty.struct.injEq] at hname
      subst hname
      obtain rfl : sd' = sd := by grind
      refine .struct hsd (fun f => by simpa using hdom f)
        fun f t' v' hft hfv => FieldValues.hasType_update htys ?_ hft hfv
      -- What is left is the *new* values: each one is a field's expression evaluated, and the type
      -- checker has already said that expression has the type the declaration gives that field.
      intro f t' v' hft hus
      obtain ⟨e', he'⟩ : ∃ e', fes.lookup f = some e' :=
        Option.isSome_iff_exists.mp (by rw [List.lookup_isSome_congr hnames f]; simp [hus])
      obtain ⟨t'', hft'', hinfer⟩ := Expression.lookup_of_inferFields hfts he'
      obtain rfl : t'' = t' := by
        have := hfields (f, t'') (List.mem_of_lookup hft'')
        grind
      exact ihev _ (List.mem_zip_of_lookup hnames he' hus) henv hinfer
  | EIndNew name c args hlen hev ihev =>
      obtain ⟨d, ts, hd, hc, hts, rfl⟩ := Expression.infer_indNew_eq_some.mp ht
      obtain ⟨hvlen, hall⟩ :=
        Value.hasType_zip_of_inferList hlen hts fun p hp t' ht' => ihev p hp henv ht'
      exact .ind hd hc hvlen hall
  | EIndMatch scrut alts _ halt _ ihscrut ihbody =>
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
  | EOptionMatchNone scrut nbody x sbody _ _ _ ihnbody =>
      obtain ⟨-, -, hnb, -⟩ := Expression.infer_optionMatch_eq_some.mp ht
      exact ihnbody henv hnb
  | EOptionMatchSome scrut nbody x sbody _ _ ihscrut ihsbody =>
      obtain ⟨t', hsc, -, hsb⟩ := Expression.infer_optionMatch_eq_some.mp ht
      -- The type of the name this case binds is the one the scrutinee's option type holds, which is
      -- the only thing the value it took apart says about what it carries.
      obtain ⟨t'', hw, heq⟩ := Value.hasType_option_some_iff.mp (ihscrut henv hsc)
      obtain rfl : t'' = t' := by simpa using heq.symm
      exact ihsbody (Env.hasType_cons hw henv) (by simpa using hsb)
  | @EListMap _ _ _ _ _ _ vs' e f _ _ hlen hat _ _ ihf ihev =>
      obtain ⟨t', r, -, hf, rfl⟩ := Expression.infer_listMap_eq_some.mp ht
      -- The function is a closure whose body was checked against a context of its own, exactly as in
      -- `EApp`, so what each call produced is of the closure's result type — which is the element
      -- type of the list the mapping built.  The list it was given contributes nothing: its element
      -- type is the function's parameter type and goes no further, so this is the one mapping rule
      -- that needs no induction hypothesis for its first operand.
      obtain ⟨cctx, r', hcenv, hbodyty, heqf⟩ := Value.hasType_closure_iff.mp (ihf henv hf)
      injection heqf with _ hr
      subst hr
      exact .list (Value.hasType_listMap hlen fun p hp =>
        ihev p hp (Env.hasType_extend (hat p hp) hcenv) (by simpa using hbodyty))
  | EHashmapPut m k v _ _ _ herase ihm ihk ihv =>
      obtain ⟨kt, vt, hm, hk, hv, -, rfl⟩ := Expression.infer_hashmapPut_eq_some.mp ht
      obtain ⟨kt', vt', hkeys, hvals, heq⟩ := Value.hasType_hashmap_iff.mp (ihm henv hm)
      obtain ⟨rfl, rfl⟩ : kt = kt' ∧ vt = vt' := by simpa using heq
      -- The new binding is typed by the induction hypotheses for the key and the value expressions;
      -- every other binding is one the map already carried, so the map's own type speaks for it.
      refine .hashmap (fun p hp => ?_) (fun p hp => ?_) <;>
        rcases List.mem_cons.mp hp with rfl | hp'
      · simpa using ihk henv hk
      · exact hkeys p (KeyValues.mem_of_erase? herase hp')
      · simpa using ihv henv hv
      · exact hvals p (KeyValues.mem_of_erase? herase hp')
  | @EHashmapGet _ _ _ o m k _ _ hlookup ihm ihk =>
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
  | @EHashmapMap _ _ _ _ _ _ kvs' m f _ _ hkeys hat _ ihm ihf ihev =>
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
  | EHashmapToList m _ ihm =>
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
  | ETupleNew es hlen hev ihev =>
      obtain ⟨ts, hts, rfl⟩ := Expression.infer_tupleNew_eq_some.mp ht
      obtain ⟨hvlen, hall⟩ :=
        Value.hasType_zip_of_inferList hlen hts fun p hp t' ht' => ihev p hp henv ht'
      exact .tuple hvlen hall
  | ETupleGet e i _ hget ihe =>
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
| EApply (args : List Value) :
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
| call (d : FuncDecl) :
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
