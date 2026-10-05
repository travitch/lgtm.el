module

public import LgtmDeepLean.Lang.IR
public import LgtmDeepLean.Lang.TypeCheck
meta import LgtmDeepLean.Lang.IR
meta import LgtmDeepLean.Lang.TypeCheck

/-! # Values and environments

What an expression evaluates *to*, and what it evaluates *in*, together with what it means for
either to agree with the types `TypeCheck.lean` assigns.  Everything here is stated without
mentioning `Eval`: the evaluation relation is one consumer of this layer, but the notion of a value
having a type, and of an environment describing a context, stands on its own. -/

public inductive Value where
| bool : Bool → Value
| int : Int → Value
| string : String → Value
/-- A value of option type, or nothing: Lean's own `Option`, since the IR's option is Lean's.

Carrying an `Option Value` rather than splitting this into two constructors is what keeps every rule
about one of these a rule about the `Option` it holds — `Value.beq?` compares two by comparing what
they hold, and `Eval`'s two match rules are the two cases of this field.  It is a nested occurrence,
exactly as `list` is, and it holds no type: an empty option is empty whatever it could have held, the
same way an empty list is, so it is `Value.HasType` that says at which type. -/
| option : Option Value → Value
| list : List Value → Value
/-- A function together with the environment it was written in: the bindings it captured and the
globals it was reached among, then the parameters and body of the `lam` itself.

The parameters are annotated the way `lam` annotates them, so a closure carries everything needed
to say what type it has.

The two halves of the environment are stored separately rather than as an `Env`, because an `Env`
holding `Value`s and a `Value` holding an `Env` would have to be declared in a `mutual` block, and
a structure declared there has neither definitional eta nor reducing projections.  `Env.closure`
is the way to build one of these from an environment, and `Env.HasType` is what says the two halves
belong together. -/
| closure : List (String × Value) → Globals → List (String × Ty) → Expression → Value
/-- An instance of the struct of the given name, with each of its fields bound to a value.

The name is all that says what this is: which fields it ought to have, and at what types, is the
business of the `StructDecl` that name resolves to, and `Value.HasType` is where the two are held
against each other.  A struct value on its own is just a name and an association list, the same way
`Ty.struct` is just a name.

The field names are spelled `String` rather than `FieldName` — the same type — because the automatic
`sizeOf` for a nested inductive treats the abbreviation as a second shape of list and then fails to
prove the two agree.  `FieldValues` is the name to use everywhere else. -/
| struct : String → List (String × Value) → Value
/-- A value of the inductive type of the given name, built by the constructor of the given name out
of one value per data type that constructor declares.

A name, a constructor and its data, and nothing else — the same way `Value.struct` is a name and its
fields.  Which constructors the type has and what each one carries is the business of the
`InductiveDecl` the type's name resolves to, and `Value.HasType` is where the two are held against
each other.

The type's name is carried as well as the constructor's because a constructor name on its own does
not say which declaration to look in, exactly as in `Expression.indNew`.  The values are positional,
because a constructor's data is: the names belong to whichever `indMatch` alternative takes this
apart. -/
| ind : String → CtorName → List Value → Value

/-- The values of the variables in scope, innermost binding first.

This could be thought of as the `Value`-level counterpart of `Context`.

It cannot be used in `Value.closure`, which is where the first such list appears: an abbreviation
mentioning `Value` has to come after it to avoid a `mutual` group that makes proofs more difficult. -/
public abbrev Bindings := List (String × Value)

/-- What a struct's fields are bound to, in the order its declaration lists them.

The `Value`-level counterpart of a `StructDecl`'s `fields`, and, like `Bindings`, an abbreviation
that cannot be used in the constructor it describes: it mentions `Value`, so it has to come after
it. -/
public abbrev FieldValues := List (FieldName × Value)

/-- `fvs` with every field `us` names rebound to the value `us` gives it: the fields `structUpdate`
produces.

Rebinding in place rather than pushing the new values in front is what keeps a struct value's fields
exactly its declaration's, in its declaration's order, however many times it is updated — so an
update changes what a field is bound to and nothing else.  That is also what makes it obviously
type-preserving: the two halves of `Value.HasType`'s struct case that talk about *which* fields there
are survive it untouched.

A field `us` names that `fvs` does not have is dropped, which is a case the type checker has already
ruled out. -/
@[expose] public def FieldValues.update (fvs us : FieldValues) : FieldValues :=
  fvs.map fun p =>
    match us.lookup p.1 with
    | some v => (p.1, v)
    | none => p

/-- What an update does to a single field: rebinds it if the update names it, leaves it alone
otherwise, and introduces nothing. -/
@[simp] public theorem FieldValues.lookup_update {fvs us : FieldValues} {f : FieldName} :
    (FieldValues.update fvs us).lookup f = (fvs.lookup f).map fun v => (us.lookup f).getD v := by
  induction fvs with
  | nil => simp [FieldValues.update]
  | cons p fvs ih =>
      obtain ⟨g, v⟩ := p
      have hhead : FieldValues.update ((g, v) :: fvs) us
          = (g, (us.lookup g).getD v) :: FieldValues.update fvs us := by
        cases hu : us.lookup g <;> simp [FieldValues.update, hu]
      rw [hhead, List.lookup_cons, List.lookup_cons]
      by_cases h : f == g
      · obtain rfl : f = g := by grind
        simp
      · simpa [h] using ih

/-! ## Structural equality

What `Expression.equals` compares two values with, and where a value of function type stops it.

It is a function rather than a rule of `Eval` because there is nothing about *evaluation* in it: two
values are the same value or they are not, and this says which, given that it can be said at all.
`Ty.comparable` is the type-level counterpart — the types from which no function type is reachable,
which are exactly the types whose values hold no closure anywhere — so an `equals` that type checks is
one this never has to give up on. -/

mutual

/-- Whether `a` and `b` are the same value, or `none` where they cannot be compared at all.

Deep and structural: two lists are equal when they hold the same values in the same order, two
options when they are both empty or both hold the same value, two struct values when they are of the
same struct and every field holds the same value, and two values of an inductive type when they are
of the same type, were built by the same constructor, and that constructor's data is the same value
for value.

A closure is what `none` is for.  Two functions are the same function when they agree on every
argument, which is a question about what they *do*: no value carries enough to settle it, and a
comparison of the bindings two closures captured would be answering something else — so a comparison
involving one has no answer here rather than a misleading one.

`none` also covers the pairs that disagree about which *type* they carry, an `int` against a `string`
or two struct values of different structs among them.  Those are pairs typing rules out as surely as
a closure is, and there is no equality between values of different types for them to be an answer
about.

What decides `false` without looking further is a difference in shape *within* one type: two lists of
different lengths, an empty option against one that holds a value, and two values of an inductive
type built by different constructors.  All are genuinely different values, and none needs anything
underneath it compared to say so. -/
@[expose] public def Value.beq? : Value → Value → Option Bool
  | .bool a, .bool b => some (a == b)
  | .int a, .int b => some (a == b)
  | .string a, .string b => some (a == b)
  | .option (some a), .option (some b) => Value.beq? a b
  | .option none, .option none => some true
  | .option _, .option _ => some false
  | .list as, .list bs => Value.beqList? as bs
  | .struct n fas, .struct m fbs => if n == m then Value.beqFields? fas fbs else none
  | .ind n c as, .ind m d bs =>
    if n == m then (if c == d then Value.beqList? as bs else some false) else none
  | _, _ => none

/-- Whether `as` and `bs` are the same values in the same order: the element type of a list and the
data of a constructor are both compared position by position, and this is the walk both take.

Lists of different lengths are different, which is the one answer reached without comparing anything.
Lists of the same length are compared throughout — the result is `none` if any pair of elements is
incomparable, rather than `false` as soon as one pair differs — so that a comparison succeeds exactly
when it could look everywhere it would have had to. -/
@[expose] public def Value.beqList? : List Value → List Value → Option Bool
  | [], [] => some true
  | a :: as, b :: bs =>
    match Value.beq? a b, Value.beqList? as bs with
    | some x, some y => some (x && y)
    | _, _ => none
  | _, _ => some false

/-- Whether two struct values' fields hold the same values: the same fields, in the same order, each
with equal values.

Positional, because two values of one struct type carry that declaration's fields in that
declaration's order — `structNew` builds them so and `FieldValues.update` rebinds without reordering
— so there is no case here where the names agree and the order does not.  Fields that disagree on a
name, or lists of different lengths, are therefore not two values of one struct type at all, and get
`none` for the reason mismatched value constructors do.

The field names are spelled `String` rather than `FieldName` for the reason `Value.struct` spells
them that way. -/
@[expose] public def Value.beqFields? : List (String × Value) → List (String × Value) →
    Option Bool
  | [], [] => some true
  | (f, a) :: fas, (g, b) :: fbs =>
    if f == g then
      match Value.beq? a b, Value.beqFields? fas fbs with
      | some x, some y => some (x && y)
      | _, _ => none
    else none
  | _, _ => none

end

mutual

/-- A comparison that has an answer gives the right one: `true` exactly when the two values are the
same value.

This is what makes the form usable in a proof.  `Eval`'s rule hands back whatever `Value.beq?` said,
so without this a `bool` that came from an `equals` would be a `bool` and nothing more; with it, the
`true` an evaluation produced *is* the two values being equal, and Lean's own `=` is what the rest of
the proof carries on with.

It is an `iff` under one hypothesis rather than two implications because both directions are the same
induction: that a comparison never reports `true` of values that differ, and that it never reports
`false` of values that do not.  Nothing is claimed where the comparison had no answer — there is no
closure in a value of a comparable type, which is the type checker's side of it.

`Value.eq_of_beq?` and `Value.ne_of_beq?` are the two halves in the form a proof applies. -/
public theorem Value.beq?_eq_some_iff : ∀ (a b : Value) (r : Bool),
    Value.beq? a b = some r → (r = true ↔ a = b)
  | .bool x, b, r => by cases b <;> simp_all [Value.beq?] <;> grind
  | .int x, b, r => by cases b <;> simp_all [Value.beq?] <;> grind
  | .string x, b, r => by cases b <;> simp_all [Value.beq?] <;> grind
  | .option oa, b, r => by
    cases b with
    | option ob =>
      cases oa with
      | none => cases ob <;> simp [Value.beq?]
      | some a =>
        cases ob with
        | none => simp [Value.beq?]
        | some b =>
          intro h
          simpa using Value.beq?_eq_some_iff a b r (by simpa [Value.beq?] using h)
    | _ => simp [Value.beq?]
  | .list as, b, r => by
    cases b with
    | list bs =>
      intro h
      simpa using Value.beqList?_eq_some_iff as bs r (by simpa [Value.beq?] using h)
    | _ => simp [Value.beq?]
  | .closure cb cg ps body, b, r => by cases b <;> simp [Value.beq?]
  | .struct n fas, b, r => by
    cases b with
    | struct m fbs =>
      intro h
      by_cases hn : n == m
      · obtain rfl : n = m := by grind
        simpa using Value.beqFields?_eq_some_iff fas fbs r (by simpa [Value.beq?] using h)
      · simp [Value.beq?, hn] at h
    | _ => simp [Value.beq?]
  | .ind n c as, b, r => by
    cases b with
    | ind m d bs =>
      intro h
      by_cases hn : n == m
      · obtain rfl : n = m := by grind
        by_cases hc : c == d
        · obtain rfl : c = d := by grind
          simpa using Value.beqList?_eq_some_iff as bs r (by simpa [Value.beq?] using h)
        · obtain rfl : r = false := by simpa [Value.beq?, hc] using h.symm
          simp only [Value.ind.injEq]
          grind
      · simp [Value.beq?, hn] at h
    | _ => simp [Value.beq?]

/-- The positional version of `Value.beq?_eq_some_iff`: the comparison of two lists that has an
answer is `true` exactly when they are the same list. -/
public theorem Value.beqList?_eq_some_iff : ∀ (as bs : List Value) (r : Bool),
    Value.beqList? as bs = some r → (r = true ↔ as = bs)
  | [], bs, r => by cases bs <;> simp [Value.beqList?]
  | a :: as, bs, r => by
    cases bs with
    | nil => simp [Value.beqList?]
    | cons b bs =>
      intro h
      rw [Value.beqList?] at h
      split at h
      · next x y hx hy =>
        obtain rfl : r = (x && y) := by grind
        rw [Bool.and_eq_true, Value.beq?_eq_some_iff a b x hx, Value.beqList?_eq_some_iff as bs y hy]
        simp
      · simp at h

/-- The by-name version of `Value.beq?_eq_some_iff`, for the field lists two struct values carry. -/
public theorem Value.beqFields?_eq_some_iff : ∀ (fas fbs : List (String × Value)) (r : Bool),
    Value.beqFields? fas fbs = some r → (r = true ↔ fas = fbs)
  | [], fbs, r => by cases fbs <;> simp [Value.beqFields?]
  | (f, a) :: fas, fbs, r => by
    cases fbs with
    | nil => simp [Value.beqFields?]
    | cons q fbs =>
      obtain ⟨g, b⟩ := q
      intro h
      rw [Value.beqFields?] at h
      split at h
      · next hfg =>
        obtain rfl : f = g := by grind
        split at h
        · next x y hx hy =>
          obtain rfl : r = (x && y) := by grind
          rw [Bool.and_eq_true, Value.beq?_eq_some_iff a b x hx,
            Value.beqFields?_eq_some_iff fas fbs y hy]
          simp
        · simp at h
      · simp at h

end

/-- Two values a comparison called equal are equal. -/
public theorem Value.eq_of_beq? {a b : Value} (h : Value.beq? a b = some true) : a = b :=
  (Value.beq?_eq_some_iff a b true h).mp rfl

/-- And two it called unequal are unequal. -/
public theorem Value.ne_of_beq? {a b : Value} (h : Value.beq? a b = some false) : a ≠ b := by
  intro heq
  simpa using (Value.beq?_eq_some_iff a b false h).mpr heq

/-- What a name is bound to while an expression runs: the local bindings, innermost first, over the
globals every expression can see.

`bindings` is ordered, and `Env.lookup` reads the first binding of a name, so pushing onto the front
shadows what was there.

`globals` holds *declarations* rather than values, which is what makes globals recursive.  A table
of values would have to contain, for each global function, a closure that had captured the table —
a value that is its own descendant, which no inductive type has.  Resolving a global's name to its
closure is deferred to `Env.lookup` instead, where the table is to hand. -/
public structure Env where
  bindings : Bindings
  globals : Globals

/-- The closure a `lam` reached in `env` evaluates to: the two halves of `env`, kept apart the way
`Value.closure` stores them. -/
@[expose] public def Env.closure (env : Env) (ps : List (String × Ty)) (body : Expression) :
    Value :=
  .closure env.bindings env.globals ps body

/-! The definitions a concrete evaluation computes with are exposed, the way `Program.lookup` and
its neighbours are: running `Eval` on an environment built out of them leaves goals like
`env.lookup "x" = some (.int 1)`, which are `rfl` only if the module the evaluation is written in
can see through every step of the way that environment was built. -/

/-- The environment a global's body runs in: no local bindings, and the same globals, so a global
can reach its siblings and itself. -/
@[expose] public def Globals.env (gs : Globals) : Env := ⟨[], gs⟩

@[simp] public theorem Globals.bindings_env (gs : Globals) : (Globals.env gs).bindings = [] := by
  simp [Globals.env]

@[simp] public theorem Globals.globals_env (gs : Globals) : (Globals.env gs).globals = gs := by
  simp [Globals.env]

/-- The value a global's name denotes: its body as a closure over the globals and nothing else.

Building this at each mention rather than once up front is what sidesteps the cyclic value a
recursive global would otherwise need. -/
@[expose] public def Globals.value (gs : Globals) (d : FuncDecl) : Value :=
  (Globals.env gs).closure d.parameters d.body

/-- The value `x` is bound to, or `none` when it is unbound.

The local bindings are searched first, so a parameter shadows a global of the same name — the same
way round as `FuncDecl.check`, which puts the parameters in front of `Globals.types`.  Keeping those
two orders together is what makes `Eval.hasType`'s variable case go through. -/
@[expose] public def Env.lookup (env : Env) (x : String) : Option Value :=
  match env.bindings.lookup x with
  | some v => some v
  | none => (env.globals.lookup x).map (Globals.value env.globals)

/-- The environment binding nothing and declaring nothing. -/
public instance : EmptyCollection Env := ⟨⟨[], []⟩⟩

@[simp] public theorem Env.bindings_empty : (∅ : Env).bindings = [] := by
  simp [EmptyCollection.emptyCollection]

@[simp] public theorem Env.globals_empty : (∅ : Env).globals = [] := by
  simp [EmptyCollection.emptyCollection]

/-- A name the bindings supply resolves to the value they give it, globals unconsulted. -/
public theorem Env.lookup_of_bindings {env : Env} {x : String} {v : Value}
    (h : env.bindings.lookup x = some v) : env.lookup x = some v := by
  simp [Env.lookup, h]

/-- A name the bindings do not supply falls through to the globals. -/
public theorem Env.lookup_of_globals {env : Env} {x : String}
    (h : env.bindings.lookup x = none) :
    env.lookup x = (env.globals.lookup x).map (Globals.value env.globals) := by
  simp [Env.lookup, h]

/-- The `Ty` a value's representation agrees with.

A list value is homogeneous: every element has the list's single element type.

An option value holds nothing or one value of the type the option type gives, so an empty one has
every option type for the reason an empty list has every list type.

A closure has a function type when its body checks against the result type under its parameters and
*some* context its captured environment agrees with.  That agreement is `Env.HasType`, but it cannot
be named here — `Env.HasType` is a definition, and it is defined in terms of `Value.HasType` — and it
cannot even be written out as it stands, because the kernel refuses a recursive occurrence under an
`∃`.  So the three halves of it are separated: the captured bindings and the context cover the same
names, and every value bound has the type promised for it.  `Value.hasType_closure_iff` puts them
back together and is the form to use.

Only the *local* bindings descend into `HasType` like that.  The globals the closure carries are
held to `Globals.WellTyped`, a condition on their syntax, precisely so that they do not: a global's
value is a closure over the globals, so typing one value-wise would ask for the same judgement
again, and this relation would have no least fixed point.

A struct value has a struct type when the name it carries is declared and its fields are that
declaration's fields at the declaration's types.  Being nominal, `Ty.struct` says only the name, so
`td.ss` is what makes this a judgement about anything at all — and unlike the context a closure's
type leaves existential, it is fixed: type declarations are a property of the whole program, so one
bundle runs through the entire relation as a parameter.

`td.ss` is where the value and the declaration are compared field by field, always by `lookup` and
never by position, so that an update — which rebinds fields without reordering them — and a
`structNew` — which writes them in the declared order — are typed by the same clauses. -/
public inductive Value.HasType (td : TypeDecls) : Value → Ty → Prop where
| bool (b : Bool) : HasType td (.bool b) .bool
| int (i : Int) : HasType td (.int i) .int
| string (s : String) : HasType td (.string s) .string
| list {vs : List Value} {t : Ty} :
    (∀ v ∈ vs, HasType td v t) → HasType td (.list vs) (.list t)
/-- An empty option has every option type, the way an empty list has every list type: there is no
value in it for a type to be required of.  Which one it has in a given place is what the annotation
on `Expression.optionNone` settles. -/
| optionNone {t : Ty} : HasType td (.option none) (.option t)
/-- And one that holds a value has the option type of that value's type. -/
| optionSome {v : Value} {t : Ty} : HasType td v t → HasType td (.option (some v)) (.option t)
| closure {cbindings : Bindings} {cglobals : Globals} {ps : Context}
    {body : Expression} {cctx : Context} {r : Ty} :
    Globals.WellTyped td cglobals →
    (∀ x, (cctx.lookup x).isSome → (cbindings.lookup x).isSome) →
    (∀ x, (cbindings.lookup x).isSome → (cctx.lookup x).isSome) →
    (∀ x t v, cctx.lookup x = some t → cbindings.lookup x = some v → HasType td v t) →
    body.infer td (ps ++ cctx ++ Globals.types cglobals) = some r →
    HasType td (.closure cbindings cglobals ps body) (.fn (ps.map Prod.snd) r)
/-- The name is declared, the value is bound at exactly the fields the declaration lists, and each
one holds a value of the type declared for it.

The two domains have to match for the same reason a closure's do: a field the declaration has not
heard of would make `structGet` on it ill typed while the value carried something anyway, and a
declared field the value lacks would make `structGet` well typed with nothing to hand back.  One
`Bool` equality says both, since neither side mentions `HasType` and so neither needs splitting the
way the closure case does. -/
| struct {name : String} {sd : StructDecl} {fvs : FieldValues} :
    td.ss.lookup name = some sd →
    (∀ f, (sd.fields.lookup f).isSome = (fvs.lookup f).isSome) →
    (∀ f t v, sd.fields.lookup f = some t → fvs.lookup f = some v → HasType td v t) →
    HasType td (.struct name fvs) (.struct name)
/-- The type's name is declared, that declaration has the constructor the value was built by, and
the value carries one value per data type that constructor takes, each of the type it takes there.

Positional where the struct case is by name, because that is how the two kinds of declaration list
what they hold: the length and the zip are what "one per data type, in order" comes to.

Recursion needs nothing extra.  A constructor may take the very type it belongs to, so this rule may
ask for a value of `.ind name` again — of a value the one in hand carries, which is smaller, so the
relation is as well founded here as it is for `list`. -/
| ind {name : String} {d : InductiveDecl} {c : CtorName} {ts : List Ty} {vs : List Value} :
    td.is.lookup name = some d →
    d.constructors.lookup c = some ts →
    vs.length = ts.length →
    (∀ p ∈ vs.zip ts, HasType td p.1 p.2) →
    HasType td (.ind name c vs) (.ind name)

/-- `env`'s globals all check, and its bindings are exactly the names `ctx` promises, at the types
`ctx` gives them.

This is the environment-level counterpart of `Value.HasType`: it is what makes a `varRef` safe to
evaluate, and it is the only thing `Eval.hasType` needs to know about an environment.

The domains have to match in *both* directions now that globals exist.  A binding the context has
not heard of would be read by `Env.lookup` in preference to a global of the same name, while
`Expression.infer` would have gone to the global for its type — so without the second clause a
stray binding could hand a `varRef` a value of the wrong type.

It is exposed, like `Globals.WellTyped`, because proofs elsewhere build one of these and take one
apart as the conjunction it is. -/
@[expose] public def Env.HasType (td : TypeDecls) (env : Env) (ctx : Context) : Prop :=
  Globals.WellTyped td env.globals
    ∧ (∀ x, (env.bindings.lookup x).isSome → (ctx.lookup x).isSome)
    ∧ (∀ x t, ctx.lookup x = some t → ∃ v, env.bindings.lookup x = some v ∧ v.HasType td t)

/-- What it takes for a closure to have a type, in terms of `Env.HasType`.

The context is existential: a closure's type says nothing about which names it captured, only that
whatever it captured was enough to type its body.

The two halves the closure stores are put back together here as the `Env` they came from, which is
what lets `Eval.hasType` hand `Env.HasType` straight to the induction hypothesis for the body. -/
@[simp] public theorem Value.hasType_closure_iff {td : TypeDecls} {cbindings : Bindings}
    {cglobals : Globals} {ps : Context} {body : Expression} {t : Ty} :
    Value.HasType td (.closure cbindings cglobals ps body) t ↔
      ∃ cctx r, Env.HasType td ⟨cbindings, cglobals⟩ cctx
        ∧ body.infer td (ps ++ cctx ++ Globals.types cglobals) = some r
        ∧ t = .fn (ps.map Prod.snd) r := by
  constructor
  · intro h
    cases h with
    | closure hgs hbinds hdom htypes hbody =>
        refine ⟨_, _, ⟨hgs, hdom, fun x t hx => ?_⟩, hbody, rfl⟩
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hbinds x (by simp [hx]))
        exact ⟨v, hv, htypes x t v hx hv⟩
  · rintro ⟨cctx, r, ⟨hgs, hdom, hval⟩, hbody, rfl⟩
    refine .closure hgs (fun x hx => ?_) hdom (fun x t v hx hv => ?_) hbody
    · obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hx
      obtain ⟨v, hv, -⟩ := hval x t ht
      simp [hv]
    · obtain ⟨v', hv', hty⟩ := hval x t hx
      grind

/-- What it takes for an empty option to have a type: the type is an option type, and that is the
whole of it.

The element type is existential and stays that way — nothing in the value constrains it — which is
exactly why `Expression.optionNone` carries an annotation. -/
@[simp] public theorem Value.hasType_option_none_iff {td : TypeDecls} {t : Ty} :
    Value.HasType td (.option none) t ↔ ∃ t', t = .option t' := by
  constructor
  · intro h
    cases h with
    | optionNone => exact ⟨_, rfl⟩
  · rintro ⟨t', rfl⟩
    exact .optionNone

/-- And what it takes for an option holding a value: the type it holds is the value's. -/
@[simp] public theorem Value.hasType_option_some_iff {td : TypeDecls} {v : Value} {t : Ty} :
    Value.HasType td (.option (some v)) t ↔
      ∃ t', Value.HasType td v t' ∧ t = .option t' := by
  constructor
  · intro h
    cases h with
    | optionSome hv => exact ⟨_, hv, rfl⟩
  · rintro ⟨t', hv, rfl⟩
    exact .optionSome hv

/-- What it takes for a struct value to have a type, as one existential over the declaration its name
resolves to.

The name is not existential the way a closure's context is: it appears in the value and in the type
alike, so a struct value has at most one type, and it is the declaration — the only thing a
`Ty.struct` does not carry — that has to be found. -/
@[simp] public theorem Value.hasType_struct_iff {td : TypeDecls} {name : String} {fvs : FieldValues}
    {t : Ty} :
    Value.HasType td (.struct name fvs) t ↔
      ∃ sd, td.ss.lookup name = some sd
        ∧ (∀ f, (sd.fields.lookup f).isSome = (fvs.lookup f).isSome)
        ∧ (∀ f t' v, sd.fields.lookup f = some t' → fvs.lookup f = some v → Value.HasType td v t')
        ∧ t = .struct name := by
  constructor
  · intro h
    cases h with
    | struct hsd hdom htys => exact ⟨_, hsd, hdom, htys, rfl⟩
  · rintro ⟨sd, hsd, hdom, htys, rfl⟩
    exact .struct hsd hdom htys

/-- What it takes for a value of an inductive type to have a type, as one existential over the
declaration its type's name resolves to and the data types its constructor takes.

Neither the type's name nor the constructor's is existential: both appear in the value, and the
type's appears in the type as well.  What has to be found is what a `Ty.ind` does not carry — the
declaration, and through it the types the constructor's data is held to. -/
@[simp] public theorem Value.hasType_ind_iff {td : TypeDecls} {name : String} {c : CtorName}
    {vs : List Value} {t : Ty} :
    Value.HasType td (.ind name c vs) t ↔
      ∃ d ts, td.is.lookup name = some d ∧ d.constructors.lookup c = some ts
        ∧ vs.length = ts.length ∧ (∀ p ∈ vs.zip ts, Value.HasType td p.1 p.2)
        ∧ t = .ind name := by
  constructor
  · intro h
    cases h with
    | ind hd hc hlen htys => exact ⟨_, _, hd, hc, hlen, htys, rfl⟩
  · rintro ⟨d, ts, hd, hc, hlen, htys, rfl⟩
    exact .ind hd hc hlen htys

/-- The values a list of expressions evaluated to have the types inference gave those expressions,
one for one and in order.

This is the positional counterpart of `Expression.lookup_of_inferFields`: a struct's fields are
matched up by name, where a constructor's data is matched up by position, so what a constructor
application needs about its arguments is stated over the zip.  It is a fact about `inferList` and an
assumption about the values, so it says nothing about *how* they were arrived at — `Eval.hasType`
supplies the assumption from its induction hypothesis. -/
public theorem Value.hasType_zip_of_inferList {td : TypeDecls} {ctx : Context}
    {es : List Expression} {vs : List Value} {ts : List Ty} (hlen : es.length = vs.length)
    (hts : Expression.inferList td ctx es = some ts)
    (hev : ∀ p ∈ es.zip vs, ∀ t, p.1.infer td ctx = some t → Value.HasType td p.2 t) :
    vs.length = ts.length ∧ ∀ p ∈ vs.zip ts, Value.HasType td p.1 p.2 := by
  induction es generalizing vs ts with
  | nil =>
      obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero hlen.symm
      simp_all
  | cons e es ih =>
      obtain ⟨t, ts', ht, hts', rfl⟩ := Expression.inferList_cons_eq_some.mp hts
      cases vs with
      | nil => simp at hlen
      | cons v vs =>
          obtain ⟨hlen', hall⟩ := ih (by simpa using hlen) hts'
            fun p hp t' ht' => hev p (List.mem_cons_of_mem _ hp) t' ht'
          refine ⟨by simpa using hlen', fun p hp => ?_⟩
          rcases List.mem_cons.mp (by simpa using hp) with rfl | hp'
          · exact hev (e, v) (by simp) t ht
          · exact hall p hp'

/-- A struct value whose fields are the declaration's fields, name for name and in order, each with a
value of its declared type, has that declaration's struct type.

This is the positional view of the struct case, and the form to build one with.  The rule itself is
stated over `lookup` so that an update — which rebinds fields without reordering them — is typed by
the same clauses as a `structNew`; but a `structNew` produces its fields in the declaration's order,
so this is the shape a concrete struct value comes in. -/
public theorem Value.hasType_struct_of_fields {td : TypeDecls} {name : String} {sd : StructDecl}
    {fvs : FieldValues} (hsd : td.ss.lookup name = some sd)
    (hnames : fvs.map Prod.fst = sd.fields.map Prod.fst)
    (hall : ∀ p ∈ fvs.zip sd.fields, Value.HasType td p.1.2 p.2.2) :
    Value.HasType td (.struct name fvs) (.struct name) :=
  .struct hsd (List.lookup_isSome_congr hnames.symm)
    fun _ _ _ hft hfv => hall _ (List.mem_zip_of_lookup hnames hfv hft)

/-- Updating preserves the types the fields are held to.

Every field of the result is either the one the struct had or the one the update gave it, so it is
enough that both agree with `fts` field by field — which is exactly what the struct's own
`Value.HasType` gives for the first and what the type checker gives for the second. -/
public theorem FieldValues.hasType_update {td : TypeDecls} {fts : List (FieldName × Ty)}
    {fvs us : FieldValues}
    (hfvs : ∀ f t v, fts.lookup f = some t → fvs.lookup f = some v → Value.HasType td v t)
    (hus : ∀ f t v, fts.lookup f = some t → us.lookup f = some v → Value.HasType td v t)
    {f : FieldName} {t : Ty} {v : Value} (hft : fts.lookup f = some t)
    (hfv : (FieldValues.update fvs us).lookup f = some v) : Value.HasType td v t := by
  rw [FieldValues.lookup_update] at hfv
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hfv
  cases h : us.lookup f with
  | none => simpa [h] using hfvs f t w hft hw
  | some v' => simpa [h] using hus f t v' hft h

/-- A globals table that checks is an environment describing the empty context: it has no local
bindings for the context to disagree with. -/
public theorem Globals.hasType_env {td : TypeDecls} {gs : Globals} (h : Globals.WellTyped td gs) :
    Env.HasType td (Globals.env gs) [] :=
  ⟨by simpa [Globals.env] using h, by simp [Globals.env], by simp⟩

/-- `env` with each name in `ps` bound to the value in `vs` at the same position, in front of what
`env` had, so the new bindings shadow it.  The globals are carried through untouched.

`List.zip` stops at the shorter list, so this only describes a call once the two are known to be the
same length; `ArgsHaveType` is what supplies that. -/
@[expose] public def Env.extend (env : Env) (ps : Context) (vs : List Value) : Env :=
  { env with bindings := (ps.map Prod.fst).zip vs ++ env.bindings }

@[simp] public theorem Env.globals_extend (env : Env) (ps : Context) (vs : List Value) :
    (env.extend ps vs).globals = env.globals := by simp [Env.extend]

/-- `ArgsHaveType ps args`: `args` are values a function with parameters `ps` can be called with,
one argument per parameter and each of the type its parameter declares.

Walking the two lists together also pins the arity down: a call passing too few or too many
arguments has no such proof. -/
public inductive ArgsHaveType (td : TypeDecls) : Context → List Value → Prop where
| nil : ArgsHaveType td [] []
| cons (x : String) :
    v.HasType td t → ArgsHaveType td ps args → ArgsHaveType td ((x, t) :: ps) (v :: args)

/-- One well-typed binding on the front of the environment and its type on the front of the context
keeps the two in step.

Both domain clauses of `Env.HasType` are settled by the same case split: the new name is in both
lists or in neither. -/
public theorem Env.hasType_cons {td : TypeDecls} {env : Env} {ctx : Context} {x : String}
    {v : Value} {t : Ty} (hv : v.HasType td t) (henv : Env.HasType td env ctx) :
    Env.HasType td ⟨(x, v) :: env.bindings, env.globals⟩ ((x, t) :: ctx) := by
  obtain ⟨hgs, hdom, hval⟩ := henv
  refine ⟨by simpa using hgs, fun y hy => ?_, fun y t' hy => ?_⟩ <;>
    simp only [List.lookup_cons] at hy ⊢ <;>
    split at hy
  · simp_all
  · simpa [show ¬ (y == x) = true by grind] using hdom y hy
  · exact ⟨v, by simp_all, by grind⟩
  · obtain ⟨v', hv', hty⟩ := hval y t' hy
    exact ⟨v', by simpa [show ¬ (y == x) = true by grind] using hv', hty⟩

/-- Binding well-typed arguments to their parameters in front of an environment gives an environment
the extended context describes.

The parameters shadow the captured environment on both sides at once — in the environment because
`Env.extend` puts them first, and in the context because they are appended on the left — which is
what keeps the two in step. -/
public theorem Env.hasType_extend {td : TypeDecls} {ps : Context} {vs : List Value} {env : Env}
    {ctx : Context} (h : ArgsHaveType td ps vs) (henv : Env.HasType td env ctx) :
    Env.HasType td (env.extend ps vs) (ps ++ ctx) := by
  induction h with
  | nil => simpa [Env.extend] using henv
  | cons _ hv _ ih => simpa [Env.extend] using Env.hasType_cons hv ih

/-- Values of a constructor's data types are arguments for parameters of those types under any names
at all, provided there is a name for each of them.

A constructor's data has no names, and a match alternative's names have no types; putting the two
lists together with `zip` is what makes a `Context` out of them, and this is what says the values
still fit. -/
public theorem ArgsHaveType.zip {td : TypeDecls} {xs : List String} {ts : List Ty}
    {vs : List Value} (hxs : xs.length = ts.length) (hvs : vs.length = ts.length)
    (hall : ∀ p ∈ vs.zip ts, Value.HasType td p.1 p.2) : ArgsHaveType td (xs.zip ts) vs := by
  induction xs generalizing ts vs with
  | nil =>
      obtain rfl : ts = [] := List.eq_nil_of_length_eq_zero hxs.symm
      obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero hvs
      exact .nil
  | cons x xs ih =>
      cases ts with
      | nil => simp at hxs
      | cons t ts =>
          cases vs with
          | nil => simp at hvs
          | cons v vs =>
              refine .cons x (hall (v, t) (by simp)) (ih (by simpa using hxs) (by simpa using hvs)
                fun p hp => hall p (by simp [hp]))

/-- Binding a constructor's values to the names a match alternative gives them describes the context
that alternative's expression is checked in.

This is `Env.hasType_extend` read for a match rather than for a call: the names and the types arrive
separately — the names from the alternative, the types from the declaration — so the context is their
zip, and the bindings are the names zipped with the values instead.  The two agree because the names
are as many as the types, which is what the type checker made sure of. -/
public theorem Env.hasType_match {td : TypeDecls} {env : Env} {ctx : Context} {xs : List String}
    {ts : List Ty} {vs : List Value} (hxs : xs.length = ts.length) (hvs : vs.length = ts.length)
    (hall : ∀ p ∈ vs.zip ts, Value.HasType td p.1 p.2) (henv : Env.HasType td env ctx) :
    Env.HasType td ⟨xs.zip vs ++ env.bindings, env.globals⟩ (xs.zip ts ++ ctx) := by
  have h := Env.hasType_extend (ArgsHaveType.zip hxs hvs hall) henv
  rwa [show env.extend (xs.zip ts) vs = ⟨xs.zip vs ++ env.bindings, env.globals⟩ by
    simp [Env.extend, List.map_fst_zip (Nat.le_of_eq hxs)]] at h

/-- The environment a call to `d` evaluates its body in: each parameter name bound to its
argument, over the globals and nothing else.

`Env.lookup` reads the first binding of a name, so a parameter repeated in `d.parameters` takes
the argument of its leftmost occurrence, and a parameter named like a global shadows it. -/
@[expose] public def FuncDecl.callEnv (d : FuncDecl) (gs : Globals) (args : List Value) : Env :=
  (Globals.env gs).extend d.parameters args

/-- Binding well-typed arguments to a declaration's parameters over its globals gives an environment
the parameter list describes.

`FuncDecl.parameters` is a `Context`, so this is what lets a call use it as one: the types the
body was written against and the types the arguments arrive with are the same list. -/
public theorem Env.hasType_callEnv {td : TypeDecls} {d : FuncDecl} {gs : Globals}
    {args : List Value} (hgs : Globals.WellTyped td gs) (h : ArgsHaveType td d.parameters args) :
    Env.HasType td (d.callEnv gs args) d.parameters := by
  simpa [FuncDecl.callEnv] using Env.hasType_extend h (Globals.hasType_env hgs)
