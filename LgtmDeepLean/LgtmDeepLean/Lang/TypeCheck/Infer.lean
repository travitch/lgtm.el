module

public import LgtmDeepLean.Lang.IR
public import LgtmDeepLean.Lang.TypeCheck.Comparable
public import LgtmDeepLean.Lang.TypeCheck.TypeDecls

/-! # Inference

`Expression.inferE` and the three walks it is mutual with, one per kind of list an expression holds,
each answering with the type it inferred or with a description of why there is none.
`Expression.infer` is that answer with the description dropped, and it is what the rest of the
development is stated over, with an inversion principle apiece: `inferE`'s body is not visible
outside this module, so those lemmas are the whole of what a proof elsewhere can use.

What an expression is inferred under is here too — `Context`, the types of the variables in scope —
along with the two conditions inference states over lists rather than over any one subexpression:
`Ty.common`, which is what makes an `indMatch`'s alternatives agree on a type, and
`Expression.altsExhaustive`, which is what makes them one apiece for the constructors.  The facts
about `List.lookup` that the struct and match rules are read through are here with them, since it is
those rules that need them.

Checking an expression against an expected type is `Expression.check`, in
`LgtmDeepLean.Lang.TypeCheck`: every form determines its own type, so checking is this module plus a
comparison. -/

/-- The types of the variables in scope, innermost binding first. -/
public abbrev Context := List (String × Ty)

/-- A name is looked up in the left half of an appended context first, so what is on the left
shadows what is on the right. -/
public theorem Context.lookup_append {ctx₁ ctx₂ : Context} {x : String} :
    (ctx₁ ++ ctx₂).lookup x =
      match ctx₁.lookup x with
      | some t => some t
      | none => ctx₂.lookup x := by
  induction ctx₁ with
  | nil => rfl
  | cons p ps ih =>
      obtain ⟨k, t⟩ := p
      by_cases h : x == k <;> simp [List.lookup_cons, h, ih]

/-- If all of the given types are the same, return that type.  Otherwise `none`.

This is used to validate that all of the branches of an `indMatch` have the same type.  If the list
is empty, also return `none`. -/
public def Ty.common : List Ty → Option Ty
  | [] => none
  | t :: ts => if ts.all (· == t) then some t else none

/-- `Ty.common` satisfies its documented behavior. -/
@[simp, grind =] public theorem Ty.common_eq_some {ts : List Ty} {t : Ty} :
    Ty.common ts = some t ↔ ts ≠ [] ∧ ∀ t' ∈ ts, t' = t := by
  cases ts with
  | nil => simp [Ty.common]
  | cons t₀ ts =>
      constructor
      · intro h
        simp only [Ty.common] at h
        split at h
        · next hall =>
            obtain rfl : t₀ = t := Option.some.inj h
            refine ⟨by simp, fun t' ht' => ?_⟩
            rcases List.mem_cons.mp ht' with rfl | ht'
            · rfl
            · simpa using List.all_eq_true.mp hall t' ht'
        · simp at h
      · rintro ⟨-, hall⟩
        obtain rfl : t₀ = t := hall t₀ (by simp)
        have hcond : (ts.all (· == t₀)) = true :=
          List.all_eq_true.mpr fun t' ht' => by simp [hall t' (List.mem_cons_of_mem _ ht')]
        simp [Ty.common, hcond]

/-! Two facts about `List.lookup` over a pair of association lists carrying the same keys in the
same order.  Every rule about a struct is stated with `lookup`, and these are what carry a fact
about one such list over to another: the field types a declaration gives, the expressions a
`structNew` gives for them, and the values those evaluate to are three lists with one key sequence
between them. -/

/-- Association lists with the same keys in the same order are defined at the same names. -/
public theorem List.lookup_isSome_congr {α β γ : Type} [BEq α] {as : List (α × β)}
    {bs : List (α × γ)} (h : as.map Prod.fst = bs.map Prod.fst) (k : α) :
    (as.lookup k).isSome = (bs.lookup k).isSome := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all
  | cons p as ih =>
      cases bs with
      | nil => simp at h
      | cons q bs =>
          obtain ⟨ka, a⟩ := p
          obtain ⟨kb, b⟩ := q
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨rfl, h⟩ := h
          by_cases hk : k == ka <;> simp [List.lookup_cons, hk, ih h]

/-- A lookup succeeds exactly for the names the list carries.

`List.lookup_isSome_congr` compares two association lists with each other; this compares one with its
own keys, which is what a fact stated over `List.Perm` — as `Expression.altsExhaustive` is — has to
be read through: a permutation says which names are there, and this is what that means for looking
one up. -/
private theorem List.lookup_isSome_iff_mem_keys {α β : Type} [BEq α] [LawfulBEq α]
    {l : List (α × β)} {k : α} : (l.lookup k).isSome ↔ k ∈ l.map Prod.fst := by
  simp only [List.lookup_isSome_iff, List.mem_map]
  grind

/-- Where two such lists both resolve a name, the entries they resolve it to are paired in the zip.

This is what turns a premise stated over `List.zip` — as `Eval`'s rules for the struct forms are,
following `EApp` — into one about the entry a `lookup` found. -/
public theorem List.mem_zip_of_lookup {α β γ : Type} [BEq α] [LawfulBEq α] {as : List (α × β)}
    {bs : List (α × γ)} {k : α} {b : β} {c : γ} (h : as.map Prod.fst = bs.map Prod.fst)
    (hb : as.lookup k = some b) (hc : bs.lookup k = some c) : ((k, b), (k, c)) ∈ as.zip bs := by
  induction as generalizing bs with
  | nil => simp at hb
  | cons p as ih =>
      cases bs with
      | nil => simp at h
      | cons q bs =>
          obtain ⟨ka, a⟩ := p
          obtain ⟨kb, b'⟩ := q
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨rfl, h⟩ := h
          rw [List.lookup_cons] at hb hc
          by_cases hk : k == ka
          · obtain rfl : k = ka := by grind
            simp only [hk] at hb hc
            simp_all
          · simp only [hk] at hb hc
            exact List.mem_cons_of_mem _ (ih h hb hc)

/-- The positional counterpart of `List.mem_zip_of_lookup`: where two lists both have an entry at
one index, those two entries are paired in the zip.

This is what a `tupleGet` is typed through, the way the struct rules are read through the `lookup`
version: a tuple's value and its type are two lists of the same length, so the value at a position
and the type at that position are a pair the `Value.HasType` premise over `List.zip` already speaks
for. -/
public theorem List.mem_zip_of_getElem? {α β : Type} {as : List α} {bs : List β} {i : Nat} {a : α}
    {b : β} (ha : as[i]? = some a) (hb : bs[i]? = some b) : (a, b) ∈ as.zip bs :=
  List.mem_of_getElem? (i := i) (by simp [List.zip, List.getElem?_zipWith, ha, hb])

/-- A lookup only ever hands back an entry the list contains, which is how a fact stated over every
entry of a table — as `Globals.WellTyped` and `structUpdate`'s typing rule both are — reaches the one
entry a name resolved to. -/
public theorem List.mem_of_lookup {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {k : α}
    {b : β} (h : l.lookup k = some b) : (k, b) ∈ l := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
      obtain ⟨k', b'⟩ := p
      rw [List.lookup_cons] at h
      split at h
      · obtain rfl : k = k' := by grind
        obtain rfl : b = b' := by grind
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)

/-! ## Exhaustiveness

What a match's alternatives have to be, as a condition on the two lists rather than on any one
alternative.  It is separate from `Expression.inferAlts` because it is not something the walk along
the alternatives can see: each alternative resolves its own constructor by name, and no alternative
knows whether the others between them covered the rest. -/

/-- The alternatives of a match expression must be exhaustive.

This is checked by validating that the constructor names of the cases are a permutation of
the constructor names in the inductive declaration. -/
@[expose] public def Expression.altsExhaustive (cs : List (CtorName × List Ty))
    (alts : List (CtorName × List String × Expression)) : Bool :=
  (alts.map Prod.fst).isPerm (cs.map Prod.fst)

/-- `Expression.altsExhaustive` is correct. -/
public theorem Expression.altsExhaustive_eq_true {cs : List (CtorName × List Ty)}
    {alts : List (CtorName × List String × Expression)} :
    Expression.altsExhaustive cs alts = true ↔ (alts.map Prod.fst).Perm (cs.map Prod.fst) := by
  simp [Expression.altsExhaustive, List.isPerm_iff]

/-- Every constructor of the declaration has an alternative (a derived fact from exhaustiveness).

This is stated over `lookup` because that is how both lists are read in `Eval.EIndMatch` and
`Value.HasType`. -/
public theorem Expression.lookup_isSome_of_altsExhaustive {cs : List (CtorName × List Ty)}
    {alts : List (CtorName × List String × Expression)}
    (h : Expression.altsExhaustive cs alts = true) {c : CtorName} (hc : (cs.lookup c).isSome) :
    (alts.lookup c).isSome :=
  List.lookup_isSome_iff_mem_keys.mpr
    ((Expression.altsExhaustive_eq_true.mp h).mem_iff.mpr (List.lookup_isSome_iff_mem_keys.mp hc))

/-- Over a declaration that names each of its constructors once, an exhaustive match names each of
its alternatives' constructors once too. -/
public theorem Expression.alts_nodup_of_altsExhaustive {cs : List (CtorName × List Ty)}
    {alts : List (CtorName × List String × Expression)} (hu : (cs.map Prod.fst).Nodup)
    (h : Expression.altsExhaustive cs alts = true) : (alts.map Prod.fst).Nodup :=
  (Expression.altsExhaustive_eq_true.mp h).nodup_iff.mpr hu

/-! ## Completeness

What the fields of a `structNew` have to be, as a condition on the two lists rather than on any one
field.  It is separate from `Expression.inferFields` for the reason `Expression.altsExhaustive` is
separate from `Expression.inferAlts`: the walk sees one field at a time, and no field knows whether
the others between them covered the rest of the declaration. -/

/-- The fields given must be the declaration's fields, each of them once and at the type declared
for it, in any order.

Two conditions where a comparison of the two lists would have been one, which is what accepting any
order costs: the names are a permutation of the declared names, the way a match's constructors are a
permutation of the declared ones, and then every field's type is the type the declaration gives it
*under its own name* rather than the type standing at its position.

Together they are as strong as that comparison was.  A field named twice makes the names no
permutation of a declaration's — which name each `lookup` would have found does not arise — and a
field the declaration does not have fails both halves at once. -/
@[expose] public def Expression.fieldsComplete (fs fts : List (FieldName × Ty)) : Bool :=
  (fts.map Prod.fst).isPerm (fs.map Prod.fst) && fts.all fun p => fs.lookup p.1 == some p.2

/-- `Expression.fieldsComplete` is correct. -/
public theorem Expression.fieldsComplete_eq_true {fs fts : List (FieldName × Ty)} :
    Expression.fieldsComplete fs fts = true ↔
      (fts.map Prod.fst).Perm (fs.map Prod.fst) ∧ ∀ p ∈ fts, fs.lookup p.1 = some p.2 := by
  simp [Expression.fieldsComplete, List.isPerm_iff]

/-- A complete field list is defined at exactly the names the declaration is (a derived fact from
the permutation half).

This is `Expression.lookup_isSome_of_altsExhaustive` for fields, and it is what the order-insensitive
half of `Value.HasType`'s struct case is discharged with: the declaration and the value agree on
*which* fields there are, which is a fact about the names alone. -/
public theorem Expression.lookup_isSome_of_fieldsComplete {fs fts : List (FieldName × Ty)}
    (h : Expression.fieldsComplete fs fts = true) (f : FieldName) :
    (fs.lookup f).isSome = (fts.lookup f).isSome :=
  Bool.eq_iff_iff.mpr <| by
    rw [List.lookup_isSome_iff_mem_keys, List.lookup_isSome_iff_mem_keys]
    exact ((Expression.fieldsComplete_eq_true.mp h).1.mem_iff).symm

/-! ## Asking for a type

The three combinators the rules are written with: one for an answer that may be missing, one for an
inferred type required to be a particular type, and one for a list of them required to be a list of
particular types.  The last two carry the name of the position they are about rather than a message
and build the message themselves, so a rule that holds pays for no string.

A subexpression that has no type at all is passed along as it stands, which is what makes the
message that comes out of a nest of forms the innermost one: every rule either reports its own
condition or repeats what it was told. -/

/-- An answer that may be missing, with what to say where it is missing: a `lookup` that resolved
nothing says no more than `none`, and this is where the reason is supplied.

The message is a function because this is on the path a well-typed program takes: a name that
resolves builds no string. -/
public def Except.ofOption {α : Type} (o : Option α) (err : Unit → String) : Except String α :=
  match o with
  | some a => .ok a
  | none => .error (err ())

/-- An inferred type required to be `t` exactly.  `what` names the position it was inferred for, as
in `the left operand of `+``. -/
public def Except.expect (r : Except String Ty) (t : Ty) (what : String) : Except String Unit :=
  match r with
  | .error m => .error m
  | .ok t' => if t' == t then .ok () else .error s!"{what} has type {t'} where {t} was expected"

/-- The first position at which two lists of types differ, with the type each gives there: what a
message about an argument list names once the list is known to be the right length. -/
private def Ty.firstMismatch : Nat → List Ty → List Ty → Option (Nat × Ty × Ty)
  | _, [], _ => none
  | _, _, [] => none
  | i, t :: ts, t' :: ts' => if t' == t then Ty.firstMismatch (i + 1) ts ts' else some (i, t, t')

/-- Two lists of types of the same length agree exactly when there is no first position at which
they differ.  This is what `Except.expectAll` decides, read as the comparison it stands for. -/
private theorem Ty.firstMismatch_eq_none {ts ts' : List Ty} (h : ts'.length = ts.length) (i : Nat) :
    Ty.firstMismatch i ts ts' = none ↔ ts' = ts := by
  induction ts generalizing ts' i with
  | nil => cases ts' <;> simp_all [Ty.firstMismatch]
  | cons t ts ih =>
      cases ts' with
      | nil => simp at h
      | cons t' ts' =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at h
          by_cases ht : t' == t <;> simp [Ty.firstMismatch, ht, ih h] <;> grind

/-- Inferred types required to be `ts`, in order.

How many there are first and then the first position where they disagree, because `Ty.fn` records
every parameter at once: a call passing too few arguments is ill typed rather than partially
applied, and that is a different thing to say than that an argument is of the wrong type. -/
public def Except.expectAll (r : Except String (List Ty)) (ts : List Ty) (what : String) :
    Except String Unit :=
  match r with
  | .error m => .error m
  | .ok ts' =>
    if ts'.length != ts.length then
      .error s!"{what} takes {ts.length} argument(s), but was given {ts'.length}"
    else
      match Ty.firstMismatch 0 ts ts' with
      | some (i, t, t') =>
        .error s!"argument {i + 1} of {what} has type {t'} where {t} was expected"
      | none => .ok ()

/-! What success comes to for each of them, which is what every inversion principle below is read
through: the message an `Except` carries says nothing about whether it carries one. -/

@[simp, grind =] public theorem Except.toOption_eq_some_iff {ε α : Type} {x : Except ε α} {a : α} :
    x.toOption = some a ↔ x = .ok a := by
  cases x <;> simp [Except.toOption]

@[simp, grind =] public theorem Except.toOption_ok {ε α : Type} {a : α} :
    (Except.ok a : Except ε α).toOption = some a := rfl

@[simp, grind =] public theorem Except.toOption_error {ε α : Type} {err : ε} :
    (Except.error err : Except ε α).toOption = (none : Option α) := rfl

@[simp, grind =] public theorem Except.toOption_ofOption {α : Type} {o : Option α}
    {err : Unit → String} : (Except.ofOption o err).toOption = o := by
  cases o <;> rfl

@[simp, grind =] public theorem Except.ofOption_eq_ok {α : Type} {o : Option α}
    {err : Unit → String} {a : α} : Except.ofOption o err = .ok a ↔ o = some a := by
  cases o <;> simp [Except.ofOption]

@[simp, grind =] public theorem Except.mapError_eq_ok {ε ε' α : Type} {f : ε → ε'}
    {x : Except ε α} {a : α} : x.mapError f = .ok a ↔ x = .ok a := by
  cases x <;> simp [Except.mapError]

@[simp, grind =] public theorem Except.bind_eq_ok {ε α β : Type} {x : Except ε α}
    {f : α → Except ε β} {b : β} : (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [Bind.bind, Except.bind]

/-- A `Unit` answer carries nothing, so all there is to know about one that succeeded is that it
did: this is what collapses the `∃` a `do` over the combinators leaves behind. -/
@[simp] public theorem Except.exists_eq_ok_unit {ε : Type} {x : Except ε Unit} :
    (∃ u, x = .ok u) ↔ x = .ok () := by
  grind

@[simp, grind =] public theorem Except.expect_eq_ok {r : Except String Ty} {t : Ty} {what : String}
    {u : Unit} : r.expect t what = .ok u ↔ r = .ok t := by
  cases r <;> simp [Except.expect]

@[simp, grind =] public theorem Except.expectAll_eq_ok {r : Except String (List Ty)} {ts : List Ty}
    {what : String} {u : Unit} : r.expectAll ts what = .ok u ↔ r = .ok ts := by
  cases r with
  | error m => simp [Except.expectAll]
  | ok ts' =>
      simp only [Except.expectAll, Except.ok.injEq]
      split
      · grind
      · next h =>
          have hlen : ts'.length = ts.length := by grind
          split <;> grind [Ty.firstMismatch_eq_none]

/-! ## What went wrong

The messages for the rules whose condition is over two lists rather than over one type.  Each of
these runs only once the condition it describes has already failed, so none of them decides
anything: what accepts or turns down a program is the condition inference had before any of it
carried a message, and these only say which entry of which list it was.  That is also why each is
total — there is always something to say, even where nothing in particular can be pointed at. -/

/-- The first field given that the declaration does not have, or does not have at the type given. -/
private def Expression.fieldProblem (name : String) (fs fts : List (FieldName × Ty)) : String :=
  match fts.find? fun p => fs.lookup p.1 != some p.2 with
  | some (f, t) =>
    match fs.lookup f with
    | some t' => s!"field '{f}' of struct '{name}' has type {t'}, but was given {t}"
    | none => s!"struct '{name}' has no field named '{f}'"
  | none => s!"the fields given are not the fields of struct '{name}'"

/-- Why the fields given are not the declaration's: one of them is wrong, or one is missing, or one
is given twice — the three things `Expression.fieldsComplete` turns down. -/
private def Expression.fieldsProblem (name : String) (fs fts : List (FieldName × Ty)) : String :=
  if fts.any fun p => fs.lookup p.1 != some p.2 then
    Expression.fieldProblem name fs fts
  else
    match fs.find? fun p => !(fts.map Prod.fst).contains p.1 with
    | some (f, _) => s!"struct '{name}' is missing field '{f}'"
    | none => s!"a field of struct '{name}' is given more than once"

/-- Why a match's alternatives are not one apiece for the constructors: one is for a constructor the
declaration does not have, or one of the declaration's has none, or one is covered twice. -/
private def Expression.altsProblem (name : String) (cs : List (CtorName × List Ty))
    (alts : List (CtorName × List String × Expression)) : String :=
  match alts.find? fun a => !(cs.map Prod.fst).contains a.1 with
  | some a => s!"'{a.1}' is not a constructor of inductive '{name}'"
  | none =>
    match cs.find? fun c => !(alts.map Prod.fst).contains c.1 with
    | some c => s!"this match has no alternative for constructor '{c.1}' of inductive '{name}'"
    | none => s!"this match has two alternatives for one constructor of inductive '{name}'"

/-- Why the types of a match's alternatives have no type in common: they disagree, or there are no
alternatives at all. -/
private def Expression.commonProblem (rs : List Ty) : String :=
  match rs with
  | [] => "this match has no alternatives, so there is no type for it to have"
  | _ => s!"the alternatives of this match have types {Ty.renderGroup rs}, which differ"

/-- Why a type cannot be a hashmap's keys: a map is read by comparing the key given against the keys
it carries, so a key type no comparison reaches the bottom of is one no lookup could answer. -/
private def Ty.keyProblem (kt : Ty) : String :=
  s!"{kt} cannot be a hashmap's key type, since values of it cannot be compared"

mutual

/-- Infer the type of `e` under `ctx`, or describe why it has none.

Every rule either reports its own condition or passes along what a subexpression reported, so what
comes out of a nest of forms names the innermost expression that nothing could be done with. -/
public def Expression.inferE (td : TypeDecls) (ctx : Context) : Expression → Except String Ty
  | .lam ps body => do
    let r ← body.inferE td (ps ++ ctx)
    .ok (.fn (ps.map Prod.snd) r)
  | .app f args =>
    match f.inferE td ctx with
    | .ok (.fn ps r) => do
      (Expression.inferListE td ctx args).expectAll ps "this call"
      .ok r
    | .ok t => .error s!"a call needs a function, but what is applied here has type {t}"
    | .error m => .error m
  | .boolLit _ => .ok .bool
  | .ite c thn els => do
    (c.inferE td ctx).expect .bool "the condition of an `if`"
    let t ← thn.inferE td ctx
    (els.inferE td ctx).expect t "the `else` branch of an `if`"
    .ok t
  | .boolAnd l r => do
    (l.inferE td ctx).expect .bool "the left operand of `&&`"
    (r.inferE td ctx).expect .bool "the right operand of `&&`"
    .ok .bool
  | .boolOr l r => do
    (l.inferE td ctx).expect .bool "the left operand of `||`"
    (r.inferE td ctx).expect .bool "the right operand of `||`"
    .ok .bool
  | .equals l r => do
    let t ← l.inferE td ctx
    (r.inferE td ctx).expect t "the right operand of `==`"
    if Ty.comparable td t then .ok .bool
    else .error s!"values of type {t} cannot be compared, so `==` does not apply to them"
  | .let_ x e body => do
    let t ← e.inferE td ctx
    body.inferE td ((x, t) :: ctx)
  | .varRef x => Except.ofOption (ctx.lookup x) fun _ => s!"no variable named '{x}' is in scope"
  | .structNew name fes => do
    let sd ← Except.ofOption (td.ss.lookup name) fun _ => s!"no struct named '{name}' is declared"
    let fts ← Expression.inferFieldsE td ctx fes
    if Expression.fieldsComplete sd.fields fts then .ok (.struct name)
    else .error (Expression.fieldsProblem name sd.fields fts)
  | .structGet e f =>
    match e.inferE td ctx with
    | .ok (.struct name) => do
      let sd ← Except.ofOption (td.ss.lookup name) fun _ => s!"no struct named '{name}' is declared"
      Except.ofOption (sd.fields.lookup f) fun _ => s!"struct '{name}' has no field named '{f}'"
    | .ok t => .error s!"a field read needs a struct, but what is read here has type {t}"
    | .error m => .error m
  | .structUpdate e fes =>
    match e.inferE td ctx with
    | .ok (.struct name) => do
      let sd ← Except.ofOption (td.ss.lookup name) fun _ => s!"no struct named '{name}' is declared"
      let fts ← Expression.inferFieldsE td ctx fes
      if fts.isEmpty then
        .error s!"a struct update must rebind at least one field of struct '{name}'"
      else if fts.all fun p => sd.fields.lookup p.1 == some p.2 then .ok (.struct name)
      else .error (Expression.fieldProblem name sd.fields fts)
    | .ok t => .error s!"a struct update needs a struct, but what is updated here has type {t}"
    | .error m => .error m
  | .indNew name c args => do
    let d ← Except.ofOption (td.is.lookup name) fun _ =>
      s!"no inductive named '{name}' is declared"
    let ts ← Except.ofOption (d.constructors.lookup c) fun _ =>
      s!"inductive '{name}' has no constructor named '{c}'"
    (Expression.inferListE td ctx args).expectAll ts s!"constructor '{c}' of inductive '{name}'"
    .ok (.ind name)
  | .indMatch scrut alts =>
    match scrut.inferE td ctx with
    | .ok (.ind name) => do
      let d ← Except.ofOption (td.is.lookup name) fun _ =>
        s!"no inductive named '{name}' is declared"
      if !Expression.altsExhaustive d.constructors alts then
        .error (Expression.altsProblem name d.constructors alts)
      else do
        let rs ← Expression.inferAltsE td ctx d.constructors alts
        Except.ofOption (Ty.common rs) fun _ => Expression.commonProblem rs
    | .ok t => .error s!"a match needs a value of an inductive type, but its scrutinee has type {t}"
    | .error m => .error m
  | .intLit _ => .ok .int
  | .plus l r => do
    (l.inferE td ctx).expect .int "the left operand of `+`"
    (r.inferE td ctx).expect .int "the right operand of `+`"
    .ok .int
  | .minus l r => do
    (l.inferE td ctx).expect .int "the left operand of `-`"
    (r.inferE td ctx).expect .int "the right operand of `-`"
    .ok .int
  | .stringLit _ => .ok .string
  | .optionNone t => .ok (.option t)
  | .optionSome e => do
    let t ← e.inferE td ctx
    .ok (.option t)
  | .optionMatch scrut nbody x sbody =>
    match scrut.inferE td ctx with
    | .ok (.option t) => do
      let r ← nbody.inferE td ctx
      (sbody.inferE td ((x, t) :: ctx)).expect r "the `some` case of an option match"
      .ok r
    | .ok t => .error s!"an option match needs an option, but its scrutinee has type {t}"
    | .error m => .error m
  | .lnil t => .ok (.list t)
  | .lcons hd tl => do
    let t ← hd.inferE td ctx
    (tl.inferE td ctx).expect (.list t) "the tail of a `::`"
    .ok (.list t)
  | .listMap l f =>
    match l.inferE td ctx with
    | .ok (.list t) =>
      match f.inferE td ctx with
      | .ok (.fn ps r) =>
        if ps == [t] then .ok (.list r)
        else .error s!"`map list` over a list of {t} needs a function of one {t} parameter, \
          but this one takes ({Ty.renderGroup ps})"
      | .ok ft => .error s!"`map list` needs a function, but its second operand has type {ft}"
      | .error m => .error m
    | .ok t => .error s!"`map list` needs a list, but its first operand has type {t}"
    | .error m => .error m
  | .listLength l =>
    match l.inferE td ctx with
    | .ok (.list _) => .ok .int
    | .ok t => .error s!"`length` needs a list, but its operand has type {t}"
    | .error m => .error m
  | .listReverse l =>
    match l.inferE td ctx with
    | .ok (.list t) => .ok (.list t)
    | .ok t => .error s!"`reverse` needs a list, but its operand has type {t}"
    | .error m => .error m
  | .hashmapEmpty kt vt =>
    if Ty.comparable td kt then .ok (.hashmap kt vt) else .error (Ty.keyProblem kt)
  | .hashmapPut m k v =>
    match m.inferE td ctx with
    | .ok (.hashmap kt vt) => do
      (k.inferE td ctx).expect kt "the key given to a hashmap update"
      (v.inferE td ctx).expect vt "the value given to a hashmap update"
      if Ty.comparable td kt then .ok (.hashmap kt vt) else .error (Ty.keyProblem kt)
    | .ok t => .error s!"a hashmap update needs a hashmap, but what is updated here has type {t}"
    | .error m => .error m
  | .hashmapGet m k =>
    match m.inferE td ctx with
    | .ok (.hashmap kt vt) => do
      (k.inferE td ctx).expect kt "the key given to a hashmap lookup"
      if Ty.comparable td kt then .ok (.option vt) else .error (Ty.keyProblem kt)
    | .ok t => .error s!"`m[k]` needs a hashmap, but what is looked up in here has type {t}"
    | .error m => .error m
  | .hashmapMap m f =>
    match m.inferE td ctx with
    | .ok (.hashmap kt vt) =>
      match f.inferE td ctx with
      | .ok (.fn ps r) =>
        if ps != [kt, vt] then
          .error s!"`map hashmap` over a {Ty.hashmap kt vt} needs a function taking \
            ({Ty.renderGroup [kt, vt]}), but this one takes ({Ty.renderGroup ps})"
        else if Ty.comparable td kt then .ok (.hashmap kt r)
        else .error (Ty.keyProblem kt)
      | .ok ft => .error s!"`map hashmap` needs a function, but its second operand has type {ft}"
      | .error m => .error m
    | .ok t => .error s!"`map hashmap` needs a hashmap, but its first operand has type {t}"
    | .error m => .error m
  | .hashmapToList m =>
    match m.inferE td ctx with
    | .ok (.hashmap kt vt) =>
      if Ty.comparable td kt then .ok (.list (.tuple [kt, vt])) else .error (Ty.keyProblem kt)
    | .ok t => .error s!"`toList` needs a hashmap, but its operand has type {t}"
    | .error m => .error m
  | .tupleNew es => do
    let ts ← Expression.inferListE td ctx es
    .ok (.tuple ts)
  | .tupleGet e i =>
    match e.inferE td ctx with
    | .ok (.tuple ts) =>
      Except.ofOption ts[i]? fun _ =>
        s!"a tuple of type {Ty.tuple ts} has no element at index {i}"
    | .ok t => .error s!"`t.{i}` needs a tuple, but what is read here has type {t}"
    | .error m => .error m

/-- Infer the types of `es`, in order, or describe why one of them has none. -/
public def Expression.inferListE (td : TypeDecls) (ctx : Context) :
    List Expression → Except String (List Ty)
  | [] => .ok []
  | e :: es => do
    let t ← e.inferE td ctx
    let ts ← Expression.inferListE td ctx es
    .ok (t :: ts)

/-- Infer the type of each field's expression, keeping the field it belongs to, or describe why one
of them has none.

The result is an association list of the fields given, in the order given, which is what lets
`structNew` compare it against a declaration's field list in one step.  `structUpdate`, which names
only some of the fields, reads it with `lookup` instead. -/
public def Expression.inferFieldsE (td : TypeDecls) (ctx : Context) :
    List (FieldName × Expression) → Except String (List (FieldName × Ty))
  | [] => .ok []
  | (f, e) :: fes => do
    let t ← (e.inferE td ctx).mapError fun m => s!"in field '{f}': {m}"
    let fts ← Expression.inferFieldsE td ctx fes
    .ok ((f, t) :: fts)

/-- Infer the type of each alternative's expression, in the order the alternatives were written, or
describe why one of them is for a constructor `cs` does not declare, binds the wrong number of
names, or has an expression with no type. -/
public def Expression.inferAltsE (td : TypeDecls) (ctx : Context) (cs : List (CtorName × List Ty)) :
    List (CtorName × List String × Expression) → Except String (List Ty)
  | [] => .ok []
  | (c, xs, body) :: alts => do
    let ts ← Except.ofOption (cs.lookup c) fun _ =>
      s!"'{c}' is not a constructor of the type being matched on"
    if xs.length != ts.length then
      .error s!"the alternative for '{c}' binds {xs.length} name(s), but '{c}' carries \
        {ts.length} value(s)"
    else do
      let t ← (body.inferE td (xs.zip ts ++ ctx)).mapError
        fun m => s!"in the alternative for '{c}': {m}"
      let rs ← Expression.inferAltsE td ctx cs alts
      .ok (t :: rs)

end

/-! ## Inference, undescribed

What the four walks above answer with the description of the failure dropped, which is the form the
rest of the development is stated over: nothing outside this module is about a message, and an
inversion principle that carried one would be a principle about which message rather than about the
program.

`Expression.inferE_eq_ok_iff` is the one fact that crosses between the two, and
`Expression.check` — in `LgtmDeepLean.Lang.TypeCheck` — is where the message is picked back up. -/

/-- Infer the type of `e` under `ctx`, or `none` if `e` is ill typed. -/
public def Expression.infer (td : TypeDecls) (ctx : Context) (e : Expression) : Option Ty :=
  (e.inferE td ctx).toOption

/-- Infer the types of `es`, in order, or `none` if any one of them is ill typed. -/
public def Expression.inferList (td : TypeDecls) (ctx : Context) (es : List Expression) :
    Option (List Ty) :=
  (Expression.inferListE td ctx es).toOption

/-- Infer the type of each field's expression, keeping the field it belongs to, or `none` if any one
of them is ill typed. -/
public def Expression.inferFields (td : TypeDecls) (ctx : Context)
    (fes : List (FieldName × Expression)) : Option (List (FieldName × Ty)) :=
  (Expression.inferFieldsE td ctx fes).toOption

/-- Infer the type of each alternative's expression, in the order the alternatives were written, or
`none` if one of them is for a constructor `cs` does not declare, binds the wrong number of names, or
has an ill-typed expression. -/
public def Expression.inferAlts (td : TypeDecls) (ctx : Context) (cs : List (CtorName × List Ty))
    (alts : List (CtorName × List String × Expression)) : Option (List Ty) :=
  (Expression.inferAltsE td ctx cs alts).toOption

/-- A type inferred is a type reported: the two forms of inference accept the same expressions at
the same types, so a fact about either of them is a fact about the other. -/
public theorem Expression.inferE_eq_ok_iff {td : TypeDecls} {ctx : Context} {e : Expression}
    {t : Ty} : e.inferE td ctx = .ok t ↔ e.infer td ctx = some t := by
  simp [Expression.infer]

/-! Inversion principles for `infer`, one per syntactic form.

`infer`'s body is not visible outside this module, so a proof elsewhere cannot unfold it and has
to go through these instead.  They are `simp` lemmas, so a hypothesis `e.infer td ctx = some t`
decomposes into premises about `e`'s subterms automatically. -/

@[simp, grind =] public theorem Expression.infer_varRef {td : TypeDecls} {ctx : Context}
    {x : String} :
    (Expression.varRef x).infer td ctx = ctx.lookup x := by
  cases h : ctx.lookup x <;> simp [Expression.infer, Expression.inferE, h]

@[simp, grind =] public theorem Expression.infer_boolLit {td : TypeDecls} {ctx : Context}
    {b : Bool} :
    (Expression.boolLit b).infer td ctx = some .bool := by
  simp [Expression.infer, Expression.inferE]

@[simp, grind =] public theorem Expression.infer_intLit {td : TypeDecls} {ctx : Context} {i : Int} :
    (Expression.intLit i).infer td ctx = some .int := by
  simp [Expression.infer, Expression.inferE]

@[simp, grind =] public theorem Expression.infer_stringLit {td : TypeDecls} {ctx : Context}
    {s : String} :
    (Expression.stringLit s).infer td ctx = some .string := by
  simp [Expression.infer, Expression.inferE]

@[simp, grind =] public theorem Expression.infer_lnil {td : TypeDecls} {ctx : Context} {t : Ty} :
    (Expression.lnil t).infer td ctx = some (.list t) := by
  simp [Expression.infer, Expression.inferE]

/-- An empty option takes its type from its annotation, the way an empty list does: there is no
value in it for an element type to be read off. -/
@[simp, grind =] public theorem Expression.infer_optionNone {td : TypeDecls} {ctx : Context}
    {t : Ty} :
    (Expression.optionNone t).infer td ctx = some (.option t) := by
  simp [Expression.infer, Expression.inferE]

/-- A `plus` is typeable exactly when both operands are `int`s, and then it is an `int`. -/
@[simp, grind =] public theorem Expression.infer_plus_eq_some {td : TypeDecls} {ctx : Context}
    {l r : Expression} {t : Ty} :
    (Expression.plus l r).infer td ctx = some t ↔
      l.infer td ctx = some .int ∧ r.infer td ctx = some .int ∧ t = .int := by
  simp [Expression.infer, Expression.inferE]
  grind

/-- A `minus` is typeable exactly when both operands are `int`s, and then it is an `int`. -/
@[simp, grind =] public theorem Expression.infer_minus_eq_some {td : TypeDecls} {ctx : Context}
    {l r : Expression} {t : Ty} :
    (Expression.minus l r).infer td ctx = some t ↔
      l.infer td ctx = some .int ∧ r.infer td ctx = some .int ∧ t = .int := by
  simp [Expression.infer, Expression.inferE]
  grind

/-- An `lcons` is typeable exactly when its tail is a list of its head's type.

This is what makes the values `Eval` builds homogeneous: the element type is read off the head
and then *required* of the tail, so one `Ty` covers every element. -/
@[simp, grind =] public theorem Expression.infer_lcons_eq_some {td : TypeDecls} {ctx : Context}
    {hd tl : Expression} {t : Ty} :
    (Expression.lcons hd tl).infer td ctx = some t ↔
      ∃ t', hd.infer td ctx = some t' ∧ tl.infer td ctx = some (.list t') ∧ t = .list t' := by
  simp [Expression.infer, Expression.inferE]
  grind

/-- A `listLength` is typeable when its operand is a list, and then it is an `int`.

The element type is existentially quantified and goes nowhere: a length counts the elements without
looking at any of them, so *which* list it is handed is all the premise says and the result's type
does not depend on it.  That is what makes this the one list form whose result is not a list —
`listReverse` passes its operand's type through, where this one discards it. -/
@[simp, grind =] public theorem Expression.infer_listLength_eq_some {td : TypeDecls}
    {ctx : Context} {l : Expression} {t : Ty} :
    (Expression.listLength l).infer td ctx = some t ↔
      (∃ t', l.infer td ctx = some (.list t')) ∧ t = .int := by
  simp only [Expression.infer, Expression.inferE, Except.toOption_eq_some_iff]
  split <;> grind

/-- A `listReverse` is typeable when its operand is a list, and then it has that same list
type.

Reversing preserves both the length and the element type, so the operand's type is also the
result's: unlike `lcons`, this form introduces no new type structure. -/
@[simp, grind =] public theorem Expression.infer_listReverse_eq_some {td : TypeDecls}
    {ctx : Context} {l : Expression} {t : Ty} :
    (Expression.listReverse l).infer td ctx = some t ↔
      ∃ t', l.infer td ctx = some (.list t') ∧ t = .list t' := by
  simp only [Expression.infer, Expression.inferE, Except.toOption_eq_some_iff]
  split <;> grind

/-- A `listMap` is typeable when its first operand is a list and its second is a function of one
parameter at that list's element type, and then it is a list of whatever that function returns.

The element type is the one thing *not* carried through to the result, which is the opposite of
`hashmapMap`: a mapping over a hashmap rebinds no key, so the key type survives and the value type
is replaced, where a list has only the one type and mapping replaces it.  The length survives
instead — one element apiece — which is what `listReverse` preserves as well.

The function takes one parameter where a hashmap's takes two, since a list element is one value
where a binding is a key beside its value.  That is also what tells the two forms apart when both
are written `map`: the arity of the function is the arity of what it is handed. -/
@[simp, grind =] public theorem Expression.infer_listMap_eq_some {td : TypeDecls} {ctx : Context}
    {l f : Expression} {t : Ty} :
    (Expression.listMap l f).infer td ctx = some t ↔
      ∃ t' r, l.infer td ctx = some (.list t') ∧ f.infer td ctx = some (.fn [t'] r)
        ∧ t = .list r := by
  simp only [Expression.infer, Expression.inferE, Except.toOption_eq_some_iff]
  split <;> simp_all <;> grind

/-- An `optionSome` is typeable exactly when the expression it holds is, and then it is an option of
that expression's type.  No annotation is needed, unlike `optionNone`: the value is what the element
type is read off, the way `lcons` reads a list's element type off its head. -/
@[simp, grind =] public theorem Expression.infer_optionSome_eq_some {td : TypeDecls} {ctx : Context}
    {e : Expression} {t : Ty} :
    (Expression.optionSome e).infer td ctx = some t ↔
      ∃ t', e.infer td ctx = some t' ∧ t = .option t' := by
  simp [Expression.infer, Expression.inferE]
  grind

/-- An `optionMatch` is typeable when its scrutinee is an option and its two cases have one type —
and then that is its type.

The same shape as `ite` rather than as `indMatch`: the cases are the two the type has, so there is
nothing to be exhaustive about and no list of inferred types to find a common one among.  What the
`some` case adds is the name it binds, which is in scope in that case alone and at the type the
scrutinee's option holds. -/
@[simp, grind =] public theorem Expression.infer_optionMatch_eq_some {td : TypeDecls}
    {ctx : Context} {scrut nbody sbody : Expression} {x : String} {t : Ty} :
    (Expression.optionMatch scrut nbody x sbody).infer td ctx = some t ↔
      ∃ t', scrut.infer td ctx = some (.option t') ∧ nbody.infer td ctx = some t
        ∧ sbody.infer td ((x, t') :: ctx) = some t := by
  simp only [Expression.infer, Expression.inferE, Except.toOption_eq_some_iff]
  split <;> simp_all

/-- A `lam` is typeable when its body is, under its parameters extended with the enclosing
context, and then it is a function from the parameters' types to the body's.

Parameters go on the front of the context, so they shadow same-named bindings from outside, and — as
in `FuncDecl.callEnv` — a name repeated in the parameter list refers to its leftmost occurrence. -/
@[simp, grind =] public theorem Expression.infer_lam_eq_some {td : TypeDecls} {ctx : Context}
    {ps : List (String × Ty)} {body : Expression} {t : Ty} :
    (Expression.lam ps body).infer td ctx = some t ↔
      ∃ r, body.infer td (ps ++ ctx) = some r ∧ t = .fn (ps.map Prod.snd) r := by
  simp [Expression.infer, Expression.inferE]
  grind

/-- An `app` is typeable when its function's type is a function type whose parameter types
are the types of the arguments, in order, and then it is that function type's result.

Because `Ty.fn` records all the parameters at once, arity is part of that one comparison: a call
passing too few arguments is ill typed rather than partially applied. -/
@[simp, grind =] public theorem Expression.infer_app_eq_some {td : TypeDecls} {ctx : Context}
    {f : Expression} {args : List Expression} {t : Ty} :
    (Expression.app f args).infer td ctx = some t ↔
      ∃ ps, f.infer td ctx = some (.fn ps t) ∧ Expression.inferList td ctx args = some ps := by
  simp only [Expression.infer, Expression.inferE, Expression.inferList]
  split <;> (try split) <;> first | grind | (simp_all <;> grind)

/-- An `ite` is typeable when its condition is a `bool` and its two branches have one type —
and then that is its type. -/
@[simp, grind =] public theorem Expression.infer_ite_eq_some {td : TypeDecls} {ctx : Context}
    {c thn els : Expression} {t : Ty} :
    (Expression.ite c thn els).infer td ctx = some t ↔
      c.infer td ctx = some .bool ∧ thn.infer td ctx = some t ∧ els.infer td ctx = some t := by
  simp [Expression.infer, Expression.inferE]

/-- A `boolAnd` is typeable exactly when both operands are `bool`s, and then it is a `bool`.

The shape `plus` and `minus` have, over `bool` rather than `int`: one type on both sides and the
same type out.  Unlike `ite`, which also asks for a `bool`, nothing here is polymorphic — the
operands are what a conditional's *condition* is, not what its branches are — and unlike `equals`
there is no comparability to ask after, since the one type this accepts is a leaf. -/
@[simp, grind =] public theorem Expression.infer_boolAnd_eq_some {td : TypeDecls} {ctx : Context}
    {l r : Expression} {t : Ty} :
    (Expression.boolAnd l r).infer td ctx = some t ↔
      l.infer td ctx = some .bool ∧ r.infer td ctx = some .bool ∧ t = .bool := by
  simp [Expression.infer, Expression.inferE]
  grind

/-- A `boolOr` is typeable exactly when both operands are `bool`s, and then it is a `bool`.

The same rule as `boolAnd`'s: the two differ in which operand's value settles the result without the
other, which is a fact about evaluating one and not about typing it. -/
@[simp, grind =] public theorem Expression.infer_boolOr_eq_some {td : TypeDecls} {ctx : Context}
    {l r : Expression} {t : Ty} :
    (Expression.boolOr l r).infer td ctx = some t ↔
      l.infer td ctx = some .bool ∧ r.infer td ctx = some .bool ∧ t = .bool := by
  simp [Expression.infer, Expression.inferE]
  grind

/-- An `equals` is typeable when its two operands are the same type and that type is one a
comparison can reach the bottom of (see `Ty.comparable`).  The `equals` itself is of type `bool`. -/
@[simp, grind =] public theorem Expression.infer_equals_eq_some {td : TypeDecls} {ctx : Context}
    {l r : Expression} {t : Ty} :
    (Expression.equals l r).infer td ctx = some t ↔
      ∃ t', l.infer td ctx = some t' ∧ r.infer td ctx = some t' ∧ Ty.comparable td t' = true
        ∧ t = .bool := by
  simp [Expression.infer, Expression.inferE]
  grind

/-- A `let_` is typeable when the expression it binds is and its body is under that name at
that type, and then it has the body's type. -/
@[simp, grind =] public theorem Expression.infer_let_eq_some {td : TypeDecls} {ctx : Context}
    {x : String} {e body : Expression} {t : Ty} :
    (Expression.let_ x e body).infer td ctx = some t ↔
      ∃ t', e.infer td ctx = some t' ∧ body.infer td ((x, t') :: ctx) = some t := by
  simp [Expression.infer, Expression.inferE]

/-- A `structNew` is typeable when the name it gives is declared and the fields it gives are that
declaration's fields, at those types, in any order.

Any order, because the fields are matched up by name: `Expression.fieldsComplete` is what says the
two lists are the same fields, and it is the only thing between this and `structUpdate`'s rule —
which is the same condition over *some* of the declaration's fields rather than all of them. -/
@[simp, grind =] public theorem Expression.infer_structNew_eq_some {td : TypeDecls} {ctx : Context}
    {name : String} {fes : List (FieldName × Expression)} {t : Ty} :
    (Expression.structNew name fes).infer td ctx = some t ↔
      ∃ sd fts, td.ss.lookup name = some sd ∧ Expression.inferFields td ctx fes = some fts
        ∧ Expression.fieldsComplete sd.fields fts = true ∧ t = .struct name := by
  simp [Expression.infer, Expression.inferE, Expression.inferFields]
  grind

/-- A `structGet` is typeable when its operand is a declared struct with the named field. -/
@[simp, grind =] public theorem Expression.infer_structGet_eq_some {td : TypeDecls} {ctx : Context}
    {e : Expression} {f : FieldName} {t : Ty} :
    (Expression.structGet e f).infer td ctx = some t ↔
      ∃ name sd, e.infer td ctx = some (.struct name) ∧ td.ss.lookup name = some sd
        ∧ sd.fields.lookup f = some t := by
  simp only [Expression.infer, Expression.inferE, Except.toOption_eq_some_iff]
  split <;> grind

/-- A `structUpdate` is typeable when its operand is a declared struct and every field it
rebinds is one of that declaration's, at the type the declaration gives it. -/
@[simp, grind =] public theorem Expression.infer_structUpdate_eq_some {td : TypeDecls}
    {ctx : Context} {e : Expression} {fes : List (FieldName × Expression)} {t : Ty} :
    (Expression.structUpdate e fes).infer td ctx = some t ↔
      ∃ name sd fts, e.infer td ctx = some (.struct name) ∧ td.ss.lookup name = some sd
        ∧ Expression.inferFields td ctx fes = some fts ∧ fts ≠ []
        ∧ (∀ p ∈ fts, sd.fields.lookup p.1 = some p.2) ∧ t = .struct name := by
  simp only [Expression.infer, Expression.inferE, Expression.inferFields]
  split <;> (try split) <;> first | grind | (simp_all <;> grind)

/-- An `indNew` is typeable when the type it names is declared, that declaration has the
constructor it names, and the arguments are the data types that constructor takes, in order. -/
@[simp, grind =] public theorem Expression.infer_indNew_eq_some {td : TypeDecls} {ctx : Context}
    {name : String} {c : CtorName} {args : List Expression} {t : Ty} :
    (Expression.indNew name c args).infer td ctx = some t ↔
      ∃ d ts, td.is.lookup name = some d ∧ d.constructors.lookup c = some ts
        ∧ Expression.inferList td ctx args = some ts ∧ t = .ind name := by
  simp [Expression.infer, Expression.inferE, Expression.inferList]
  grind

/-- An `indMatch` is typeable when its scrutinee is a declared inductive type, it has one
alternative per constructor of that declaration, those alternatives all check, and they all have one
type. -/
@[simp, grind =] public theorem Expression.infer_indMatch_eq_some {td : TypeDecls} {ctx : Context}
    {scrut : Expression} {alts : List (CtorName × List String × Expression)} {t : Ty} :
    (Expression.indMatch scrut alts).infer td ctx = some t ↔
      ∃ name d rs, scrut.infer td ctx = some (.ind name) ∧ td.is.lookup name = some d
        ∧ Expression.altsExhaustive d.constructors alts = true
        ∧ Expression.inferAlts td ctx d.constructors alts = some rs ∧ rs ≠ []
        ∧ ∀ t' ∈ rs, t' = t := by
  simp only [Expression.infer, Expression.inferE, Expression.inferAlts]
  repeat' split
  all_goals first | grind | (simp_all <;> grind)

/-! The five hashmap forms.  Each of them asks for the key type to be comparable, which is the one
condition that is not about the shape of the expression: a hashmap is read by comparing the key
given against the keys the map carries, so a key type `Ty.comparable` turns down is one no `get`
could answer and no `put` could rebind over.  It is required of the empty map, of `map` and of
`toList` as well — none of which compares a key — so that a hashmap type nothing could do anything
with is not reachable by building one. -/

/-- A `hashmapEmpty` takes its type from its two annotations, the way an empty list and an empty
option take theirs: it binds nothing, so there is no key and no value for either half to be read
off. -/
@[simp, grind =] public theorem Expression.infer_hashmapEmpty_eq_some {td : TypeDecls}
    {ctx : Context} {kt vt t : Ty} :
    (Expression.hashmapEmpty kt vt).infer td ctx = some t ↔
      Ty.comparable td kt = true ∧ t = .hashmap kt vt := by
  simp only [Expression.infer, Expression.inferE, Except.toOption_eq_some_iff]
  split <;> grind

/-- A `hashmapPut` is typeable when its first operand is a hashmap and the key and value it is given
are of the two types that hashmap relates — and then it is that same hashmap type.

Rebinding introduces no type structure, so the result's type is the map's, the way `listReverse`'s
is its operand's. -/
@[simp, grind =] public theorem Expression.infer_hashmapPut_eq_some {td : TypeDecls} {ctx : Context}
    {m k v : Expression} {t : Ty} :
    (Expression.hashmapPut m k v).infer td ctx = some t ↔
      ∃ kt vt, m.infer td ctx = some (.hashmap kt vt) ∧ k.infer td ctx = some kt
        ∧ v.infer td ctx = some vt ∧ Ty.comparable td kt = true ∧ t = .hashmap kt vt := by
  simp only [Expression.infer, Expression.inferE, Except.toOption_eq_some_iff]
  split <;> simp_all <;> grind

/-- A `hashmapGet` is typeable when its first operand is a hashmap and its second is a key of that
hashmap's key type, and then it is an option of its value type.

An option rather than the value type itself, because a key the map does not bind is not an error:
`optionMatch` is what the two cases are read with, so a lookup that found nothing is a value like
any other. -/
@[simp, grind =] public theorem Expression.infer_hashmapGet_eq_some {td : TypeDecls} {ctx : Context}
    {m k : Expression} {t : Ty} :
    (Expression.hashmapGet m k).infer td ctx = some t ↔
      ∃ kt vt, m.infer td ctx = some (.hashmap kt vt) ∧ k.infer td ctx = some kt
        ∧ Ty.comparable td kt = true ∧ t = .option vt := by
  simp only [Expression.infer, Expression.inferE, Except.toOption_eq_some_iff]
  split <;> simp_all <;> grind

/-- A `hashmapMap` is typeable when its first operand is a hashmap and its second is a function of
that hashmap's two types, and then it is a hashmap from the same keys to whatever that function
returns.

The function takes the key as well as the value, so its parameter types are the map's two in that
order: `tuple [kt, vt]` is what a binding is where `toList` produces one, and this is the same pair
read as a parameter list.  The key type is the one thing carried through to the result — a mapping
rebinds no key — so what the two hashmap types share is exactly what is not mapped. -/
@[simp, grind =] public theorem Expression.infer_hashmapMap_eq_some {td : TypeDecls} {ctx : Context}
    {m f : Expression} {t : Ty} :
    (Expression.hashmapMap m f).infer td ctx = some t ↔
      ∃ kt vt r, m.infer td ctx = some (.hashmap kt vt) ∧ f.infer td ctx = some (.fn [kt, vt] r)
        ∧ Ty.comparable td kt = true ∧ t = .hashmap kt r := by
  simp only [Expression.infer, Expression.inferE, Except.toOption_eq_some_iff]
  split <;> simp_all <;> grind

/-- A `hashmapToList` is typeable when its operand is a hashmap, and then it is a list of the tuple
of that hashmap's two types: one element per binding, each a key beside the value it is bound to.

The map's own type is what both halves of the element type come from, so this form reads no
expression but the map's — there is no key here to require anything of.  `tuple [kt, vt]` rather
than two parallel lists because a binding is a key *and* its value: nothing else in the IR relates
the two, so taking them apart into a list of keys and a list of values would lose which went with
which. -/
@[simp, grind =] public theorem Expression.infer_hashmapToList_eq_some {td : TypeDecls}
    {ctx : Context} {m : Expression} {t : Ty} :
    (Expression.hashmapToList m).infer td ctx = some t ↔
      ∃ kt vt, m.infer td ctx = some (.hashmap kt vt) ∧ Ty.comparable td kt = true
        ∧ t = .list (.tuple [kt, vt]) := by
  simp only [Expression.infer, Expression.inferE, Except.toOption_eq_some_iff]
  split <;> simp_all <;> grind

/-! The two tuple forms.  Neither asks for anything the expression does not carry: a tuple type
holds the types it relates, so there is no declaration to resolve the way the struct and inductive
forms have one, and no comparability condition the way the hashmap forms have one. -/

/-- A `tupleNew` is typeable exactly when every element is, and then it is the tuple of their types
in the order they were written.

It takes no annotation, unlike `lnil` and `optionNone` and `hashmapEmpty`: the elements are what the
types are read off, and `tupleNew []` needs none either — `tuple []` is the only type it could
have. -/
@[simp, grind =] public theorem Expression.infer_tupleNew_eq_some {td : TypeDecls} {ctx : Context}
    {es : List Expression} {t : Ty} :
    (Expression.tupleNew es).infer td ctx = some t ↔
      ∃ ts, Expression.inferList td ctx es = some ts ∧ t = .tuple ts := by
  simp [Expression.infer, Expression.inferE, Expression.inferList]
  grind

/-- A `tupleGet` is typeable when its operand is a tuple with an element at that index, and then it
has the type that tuple type gives at it.

The index is read off the expression rather than evaluated, which is what lets one `Ty` come out of
a heterogeneous value: `getElem?` is a lookup in the *type*, so an index past the end is ill typed
rather than a failure at run time.  That is the positional reading of `structGet`, whose field name
is looked up in the declaration the operand's type names. -/
@[simp, grind =] public theorem Expression.infer_tupleGet_eq_some {td : TypeDecls} {ctx : Context}
    {e : Expression} {i : Nat} {t : Ty} :
    (Expression.tupleGet e i).infer td ctx = some t ↔
      ∃ ts, e.infer td ctx = some (.tuple ts) ∧ ts[i]? = some t := by
  simp only [Expression.infer, Expression.inferE, Except.toOption_eq_some_iff]
  split <;> grind

/-! Inversion principles for `inferList`.  Together these say what it computes: the argument types
in order, and `none` as soon as one argument has no type. -/

@[simp, grind =] public theorem Expression.inferList_nil {td : TypeDecls} {ctx : Context} :
    Expression.inferList td ctx [] = some [] := by
  simp [Expression.inferList, Expression.inferListE]

@[simp, grind =] public theorem Expression.inferList_cons_eq_some {td : TypeDecls} {ctx : Context}
    {e : Expression} {es : List Expression} {ts : List Ty} :
    Expression.inferList td ctx (e :: es) = some ts ↔
      ∃ t ts', e.infer td ctx = some t ∧ Expression.inferList td ctx es = some ts'
        ∧ ts = t :: ts' := by
  simp [Expression.inferList, Expression.inferListE, Expression.infer]
  grind

/-! Inversion principles for `inferFields`, and then what it says about the list it produces: the
fields it was given, in order, and `none` as soon as one field's expression has no type. -/

@[simp, grind =] public theorem Expression.inferFields_nil {td : TypeDecls} {ctx : Context} :
    Expression.inferFields td ctx [] = some [] := by
  simp [Expression.inferFields, Expression.inferFieldsE]

@[simp, grind =] public theorem Expression.inferFields_cons_eq_some {td : TypeDecls} {ctx : Context}
    {f : FieldName} {e : Expression} {fes : List (FieldName × Expression)}
    {fts : List (FieldName × Ty)} :
    Expression.inferFields td ctx ((f, e) :: fes) = some fts ↔
      ∃ t fts', e.infer td ctx = some t ∧ Expression.inferFields td ctx fes = some fts'
        ∧ fts = (f, t) :: fts' := by
  simp [Expression.inferFields, Expression.inferFieldsE, Expression.infer]
  grind

/-- Inference renames nothing: the fields it reports are the fields it was given, in that order.

This is the fact that ties the three lists a `structNew` involves together.  Its declaration's fields
are `inferFields`' output, the expressions are its input, and `Eval` relates those to the values, so
one key sequence runs through all four. -/
public theorem Expression.map_fst_of_inferFields {td : TypeDecls} {ctx : Context}
    {fes : List (FieldName × Expression)} {fts : List (FieldName × Ty)}
    (h : Expression.inferFields td ctx fes = some fts) :
    fts.map Prod.fst = fes.map Prod.fst := by
  induction fes generalizing fts with
  | nil => simp_all
  | cons p fes ih =>
      obtain ⟨f, e⟩ := p
      obtain ⟨t, fts', -, hfts, rfl⟩ := Expression.inferFields_cons_eq_some.mp h
      simp [ih hfts]

/-- The type `inferFields` reports for a field is the type of the expression that field was given.

Stated over `lookup` rather than position because that is how both struct rules read the list: a
field's expression is found by name, and the type beside it is the one that field has. -/
public theorem Expression.lookup_of_inferFields {td : TypeDecls} {ctx : Context}
    {fes : List (FieldName × Expression)} {fts : List (FieldName × Ty)}
    (h : Expression.inferFields td ctx fes = some fts) {f : FieldName} {e : Expression}
    (hf : fes.lookup f = some e) : ∃ t, fts.lookup f = some t ∧ e.infer td ctx = some t := by
  induction fes generalizing fts with
  | nil => simp at hf
  | cons p fes ih =>
      obtain ⟨g, e'⟩ := p
      obtain ⟨t, fts', he', hfts, rfl⟩ := Expression.inferFields_cons_eq_some.mp h
      rw [List.lookup_cons] at hf ⊢
      split at hf
      · exact ⟨t, by simp_all, by grind⟩
      · exact ih hfts hf

/-! Inversion principles for `inferAlts`.  There is one alternative list to run out, and the second
says what one step along it asks for. -/

@[simp, grind =] public theorem Expression.inferAlts_nil {td : TypeDecls} {ctx : Context}
    {cs : List (CtorName × List Ty)} : Expression.inferAlts td ctx cs [] = some [] := by
  simp [Expression.inferAlts, Expression.inferAltsE]

/-- One step of the walk: the alternative is for a constructor the declaration has, it binds one
name per data type that constructor carries, and its expression is typeable under those names at
those types. -/
@[simp, grind =] public theorem Expression.inferAlts_cons_eq_some {td : TypeDecls} {ctx : Context}
    {cs : List (CtorName × List Ty)} {c : CtorName} {xs : List String} {body : Expression}
    {alts : List (CtorName × List String × Expression)} {rs : List Ty} :
    Expression.inferAlts td ctx cs ((c, xs, body) :: alts) = some rs ↔
      ∃ ts t rs', cs.lookup c = some ts ∧ xs.length = ts.length
        ∧ body.infer td (xs.zip ts ++ ctx) = some t
        ∧ Expression.inferAlts td ctx cs alts = some rs' ∧ rs = t :: rs' := by
  simp [Expression.inferAlts, Expression.inferAltsE, Expression.infer]
  grind

/-- The alternative a constructor's name resolves to is the one checked against that constructor's
data types, and the type inferred for its expression is one of the types `inferAlts` reports. -/
public theorem Expression.lookup_of_inferAlts {td : TypeDecls} {ctx : Context}
    {cs : List (CtorName × List Ty)} {alts : List (CtorName × List String × Expression)}
    {rs : List Ty} (h : Expression.inferAlts td ctx cs alts = some rs) {c : CtorName}
    {ts : List Ty} {xs : List String} {body : Expression} (hc : cs.lookup c = some ts)
    (ha : alts.lookup c = some (xs, body)) :
    ∃ t, t ∈ rs ∧ xs.length = ts.length ∧ body.infer td (xs.zip ts ++ ctx) = some t := by
  induction alts generalizing rs with
  | nil => simp at ha
  | cons q alts ih =>
      obtain ⟨c₀, xs₀, body₀⟩ := q
      obtain ⟨ts₀, t₀, rs', hc₀, hlen, hbody, halts, rfl⟩ := Expression.inferAlts_cons_eq_some.mp h
      rw [List.lookup_cons] at ha
      by_cases hcc : c == c₀
      · obtain rfl : c = c₀ := by grind
        simp only [hcc] at ha
        obtain ⟨rfl, rfl⟩ : xs = xs₀ ∧ body = body₀ := by grind
        obtain rfl : ts = ts₀ := by grind
        exact ⟨t₀, by simp, hlen, hbody⟩
      · simp only [hcc] at ha
        obtain ⟨t, htmem, htlen, htbody⟩ := ih halts ha
        exact ⟨t, List.mem_cons_of_mem _ htmem, htlen, htbody⟩
