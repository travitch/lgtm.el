module

public import LgtmDeepLean.Lang.Eval

/-! # Determinism

`Eval` is a relation, and nothing said so far rules out one expression having two values.  Several
things in this development are shaped by that: `Progress.lean`'s `Stuck.not_*` family asks its
callers for hypotheses over *every* value a subexpression can produce, because the value a `Stuck`
premise produced need not be the one the caller has in hand.

`Eval.unique` is what closes that gap, and `Eval.not_stuck` is what it buys: a declaration's
progress proof becomes a corollary of the proof that it has a value, rather than the same induction
written a second time for failure. -/

/-- Two value lists that are pointwise determined by the same expression list are equal.

This is the one helper the rules with a `List.zip` premise share — `EApp`, `EIndNew`, `ETupleNew`,
`EListMap`, `EListFlatMap` and `EListSortOn` all evaluate one subexpression per element and pin the
lengths separately, because `List.zip` stops at the shorter list.

`h` is stated over the two zips at once rather than over a relation the two lists are pointwise in,
so that nothing here has to be told what that relation is: a caller spends the induction hypothesis
of its own premise at `p` and the other derivation's premise at `q`, and `p.1 = q.1` is what says
the two speak of one position. -/
public theorem List.eq_of_zip_unique {α β : Type} {xs : List α} {vs ws : List β}
    (hv : xs.length = vs.length) (hw : xs.length = ws.length)
    (h : ∀ p ∈ xs.zip vs, ∀ q ∈ xs.zip ws, p.1 = q.1 → p.2 = q.2) : vs = ws := by
  induction xs generalizing vs ws with
  | nil =>
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by simpa using hv.symm)
    exact (List.eq_nil_of_length_eq_zero (by simpa using hw.symm)).symm
  | cons x xs ih =>
    cases vs with
    | nil => simp at hv
    | cons v vs =>
      cases ws with
      | nil => simp at hw
      | cons u ws =>
        obtain rfl : v = u := h (x, v) (by simp) (x, u) (by simp) rfl
        exact congrArg (v :: ·) (ih (by simpa using hv) (by simpa using hw)
          fun p hp q hq hpq =>
            h p (by simp [List.zip_cons_cons, hp]) q (by simp [List.zip_cons_cons, hq]) hpq)

/-- The same where the lists carry a key beside each value, which is the shape the three keyed rules
take: `EStructNew`, `EStructUpdate` and `EHashmapMap` pin the keys with a `List.map Prod.fst`
equation rather than the lengths, and evaluate one subexpression per value.  So the keys come from
`hkeys` and the values from `h`, and between them they settle the whole list. -/
public theorem List.eq_of_zip_snd_unique {α κ β : Type} {xs : List α} {vs ws : List (κ × β)}
    (hv : xs.length = vs.length) (hkeys : vs.map Prod.fst = ws.map Prod.fst)
    (h : ∀ p ∈ xs.zip vs, ∀ q ∈ xs.zip ws, p.1 = q.1 → p.2.2 = q.2.2) : vs = ws := by
  induction xs generalizing vs ws with
  | nil =>
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by simpa using hv.symm)
    simp only [List.map_nil] at hkeys
    exact (List.map_eq_nil_iff.mp hkeys.symm).symm
  | cons x xs ih =>
    cases vs with
    | nil => simp at hv
    | cons v vs =>
      cases ws with
      | nil => simp at hkeys
      | cons u ws =>
        obtain ⟨kv, bv⟩ := v
        obtain ⟨ku, bu⟩ := u
        rw [List.map_cons, List.map_cons, List.cons.injEq] at hkeys
        obtain ⟨rfl, hkeys⟩ := hkeys
        obtain rfl : bv = bu := h (x, kv, bv) (by simp) (x, kv, bu) (by simp) rfl
        exact congrArg ((kv, bv) :: ·) (ih (by simpa using hv) hkeys
          fun p hp q hq hpq =>
            h p (by simp [List.zip_cons_cons, hp]) q (by simp [List.zip_cons_cons, hq]) hpq)

/-- An element of a list as long as another is paired with one of that other's elements.

Which is what reads a premise stated over a zip — one evaluation per element — back as a fact about
*one* element, the way `Stuck`'s rules for the list forms name the single element whose call went
wrong.  `Eval.not_stuck` spends this at every such rule. -/
public theorem List.exists_mem_zip_left {α β : Type} {xs : List α} {ys : List β} {x : α}
    (hlen : xs.length = ys.length) (hx : x ∈ xs) : ∃ y, (x, y) ∈ xs.zip ys := by
  induction xs generalizing ys with
  | nil => simp at hx
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys =>
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨b, by simp⟩
      · obtain ⟨y, hy⟩ := ih (by simpa using hlen) hx'
        exact ⟨y, by simp [List.zip_cons_cons, hy]⟩

/-- Where two decompositions of one list name different positions, the element the earlier one names
belongs to the other's prefix. -/
public theorem List.mem_of_append_cons_eq {α : Type} {as bs cs ds : List α} {a b : α}
    (h : as ++ a :: cs = bs ++ b :: ds) (hlt : as.length < bs.length) : a ∈ bs := by
  have hidx : (as ++ a :: cs)[as.length]? = some a := by
    rw [List.getElem?_append_right (Nat.le_refl _)]
    simp
  rw [h, List.getElem?_append_left hlt] at hidx
  exact List.mem_of_getElem? hidx

/-- So two decompositions that each name an element the other's prefix does not contain name the
same position.

This is what the two `listFindIndex` rules need of each other: both say "the first element the
predicate accepted", and two searches that stopped at different elements would each have put the
other's element among the ones it had already answered `false` for. -/
public theorem List.length_eq_of_append_cons_eq {α : Type} {as bs cs ds : List α} {a b : α}
    (h : as ++ a :: cs = bs ++ b :: ds) (ha : a ∉ bs) (hb : b ∉ as) : as.length = bs.length := by
  rcases Nat.lt_trichotomy as.length bs.length with hlt | heq | hgt
  · exact absurd (List.mem_of_append_cons_eq h hlt) ha
  · exact heq
  · exact absurd (List.mem_of_append_cons_eq h.symm hgt) hb

/-! ### Lists of a known length

`List.length_eq_one_iff` is Lean core's; the two beside it are not, and they are what a proof reading
the arguments of a concrete call wants — `FuncDecl.apply_of_eval_app` hands back a list whose length
is all that is known of it, and a body passing two or three arguments is the common case.  Core has
`List.eq_getElem_of_length_eq_two`, which answers the same question as an equation between indexed
reads rather than as the existential a `rcases` would leave; these are the existential form.

Stated as `iff`s, the way core's one-element version is, so that either direction is to hand: the
forward one destructures and the backward one is how a caller discharges a length premise. -/

public theorem List.length_eq_two_iff {α : Type} {l : List α} :
    l.length = 2 ↔ ∃ a b, l = [a, b] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp_all

public theorem List.length_eq_three_iff {α : Type} {l : List α} :
    l.length = 3 ↔ ∃ a b c, l = [a, b, c] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩ <;> simp_all

/-- `Eval` is deterministic: an expression has at most one value under one environment.

This is what makes the refutation half of a progress proof a corollary of the construction half
rather than a mirror of it — see `Eval.not_stuck`, whose mismatch cases are exactly the places that
need the value a `Stuck` premise produced identified with the one the derivation at hand produced.

The proof is an induction on one derivation and an inversion on the other, and the expression
settles which rule the other derivation used — so most cases are the subderivations' induction
hypotheses and nothing else.  Three groups cost more:

* the rules with a `List.zip` premise go through `List.eq_of_zip_unique` and
  `List.eq_of_zip_snd_unique`, which is that premise's induction hypothesis spent once rather than
  eight times;
* `EListFindIndexSome` against itself needs more than the subderivations: two searches may stop at
  different elements, and ruling that out is `List.length_eq_of_append_cons_eq` over the observation
  that the earlier element would then have to answer both `true` and `false`;
* `EListSortBy` is the one case that needs a fact about the function the rule computes with.  The
  rule holds an arbitrary `cmp : Value → Value → Bool` to the DSL function only at pairs drawn from
  the list, so two derivations produce `Value.sortWith` of two comparisons that agree only there.
  `Value.sortWith_congr` — and `List.mergeSort_congr` under it, which Lean core does not have — is
  what closes that gap. -/
public theorem Eval.unique {td : TypeDecls} {env : Env} {e : Expression} {v w : Value}
    (h₁ : Eval td env e v) (h₂ : Eval td env e w) : v = w := by
  induction h₁ generalizing w with
  | ELam ps body => cases h₂; rfl
  | EApp f args hf hlen hargs hat hbody ihf ihargs ihbody =>
    cases h₂ with
    | EApp _ _ hf' hlen' hargs' _ hbody' =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (ihf hf')
      obtain rfl :=
        List.eq_of_zip_unique hlen hlen'
          fun p hp q hq hpq => ihargs p hp (by rw [hpq]; exact hargs' q hq)
      exact ihbody hbody'
  | EBoolLit b => cases h₂; rfl
  | EIteTrue c thn els hc hthn ihc ihthn =>
    cases h₂ with
    | EIteTrue _ _ _ _ hthn' => exact ihthn hthn'
    | EIteFalse _ _ _ hc' _ => exact absurd (ihc hc') (by simp)
  | EIteFalse c thn els hc hels ihc ihels =>
    cases h₂ with
    | EIteTrue _ _ _ hc' _ => exact absurd (ihc hc') (by simp)
    | EIteFalse _ _ _ _ hels' => exact ihels hels'
  | EBoolAndFalse l r hl ihl =>
    cases h₂ with
    | EBoolAndFalse _ _ _ => rfl
    | EBoolAndTrue _ _ hl' _ => exact absurd (ihl hl') (by simp)
  | EBoolAndTrue l r hl hr ihl ihr =>
    cases h₂ with
    | EBoolAndFalse _ _ hl' => exact absurd (ihl hl') (by simp)
    | EBoolAndTrue _ _ _ hr' => exact ihr hr'
  | EBoolOrTrue l r hl ihl =>
    cases h₂ with
    | EBoolOrTrue _ _ _ => rfl
    | EBoolOrFalse _ _ hl' _ => exact absurd (ihl hl') (by simp)
  | EBoolOrFalse l r hl hr ihl ihr =>
    cases h₂ with
    | EBoolOrTrue _ _ hl' => exact absurd (ihl hl') (by simp)
    | EBoolOrFalse _ _ _ hr' => exact ihr hr'
  | EEquals l r hl hr hbeq ihl ihr =>
    cases h₂ with
    | EEquals _ _ hl' hr' hbeq' =>
      obtain rfl := ihl hl'
      obtain rfl := ihr hr'
      exact congrArg Value.bool (Option.some.inj (hbeq.symm.trans hbeq'))
  | ELt l r hl hr hlt ihl ihr =>
    cases h₂ with
    | ELt _ _ hl' hr' hlt' =>
      obtain rfl := ihl hl'
      obtain rfl := ihr hr'
      exact congrArg Value.bool (Option.some.inj (hlt.symm.trans hlt'))
  | ELe l r hl hr hle ihl ihr =>
    cases h₂ with
    | ELe _ _ hl' hr' hle' =>
      obtain rfl := ihl hl'
      obtain rfl := ihr hr'
      exact congrArg Value.bool (Option.some.inj (hle.symm.trans hle'))
  | ELet x e body he hbody ihe ihbody =>
    cases h₂ with
    | ELet _ _ _ he' hbody' =>
      obtain rfl := ihe he'
      exact ihbody hbody'
  | EVarRef x hx => exact Option.some.inj (hx.symm.trans (Eval.varRef_inv h₂))
  | EStructNew name fes hnames hev ihev =>
    cases h₂ with
    | EStructNew _ _ hnames' hev' =>
      obtain rfl :=
        List.eq_of_zip_snd_unique (by simpa using congrArg List.length hnames)
          (hnames.symm.trans hnames')
          fun p hp q hq hpq => ihev p hp (by rw [hpq]; exact hev' q hq)
      rfl
  | EStructGet e f he hf ihe =>
    cases h₂ with
    | EStructGet _ _ he' hf' =>
      obtain ⟨rfl, rfl⟩ := Value.struct.inj (ihe he')
      exact Option.some.inj (hf.symm.trans hf')
  | EStructUpdate e fes he hnames hev ihe ihev =>
    cases h₂ with
    | EStructUpdate _ _ he' hnames' hev' =>
      obtain ⟨rfl, rfl⟩ := Value.struct.inj (ihe he')
      obtain rfl :=
        List.eq_of_zip_snd_unique (by simpa using congrArg List.length hnames)
          (hnames.symm.trans hnames')
          fun p hp q hq hpq => ihev p hp (by rw [hpq]; exact hev' q hq)
      rfl
  | EIndNew name c args hlen hev ihev =>
    cases h₂ with
    | EIndNew _ _ _ hlen' hev' =>
      obtain rfl :=
        List.eq_of_zip_unique hlen hlen'
          fun p hp q hq hpq => ihev p hp (by rw [hpq]; exact hev' q hq)
      rfl
  | EIndMatch scrut alts hscrut hlookup hbody ihscrut ihbody =>
    cases h₂ with
    | EIndMatch _ _ hscrut' hlookup' hbody' =>
      obtain ⟨rfl, rfl, rfl⟩ := Value.ind.inj (ihscrut hscrut')
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hlookup.symm.trans hlookup'))
      exact ihbody hbody'
  | EIntLit i => cases h₂; rfl
  | EPlus e₁ e₂ h1 h2 ih1 ih2 =>
    cases h₂ with
    | EPlus _ _ h1' h2' =>
      obtain rfl := Value.int.inj (ih1 h1')
      obtain rfl := Value.int.inj (ih2 h2')
      rfl
  | EMinus e₁ e₂ h1 h2 ih1 ih2 =>
    cases h₂ with
    | EMinus _ _ h1' h2' =>
      obtain rfl := Value.int.inj (ih1 h1')
      obtain rfl := Value.int.inj (ih2 h2')
      rfl
  | EMin e₁ e₂ h1 h2 ih1 ih2 =>
    cases h₂ with
    | EMin _ _ h1' h2' =>
      obtain rfl := Value.int.inj (ih1 h1')
      obtain rfl := Value.int.inj (ih2 h2')
      rfl
  | EMax e₁ e₂ h1 h2 ih1 ih2 =>
    cases h₂ with
    | EMax _ _ h1' h2' =>
      obtain rfl := Value.int.inj (ih1 h1')
      obtain rfl := Value.int.inj (ih2 h2')
      rfl
  | EStringLit s => cases h₂; rfl
  | ENone ty => cases h₂; rfl
  | ESome e he ihe =>
    cases h₂ with
    | ESome _ he' =>
      obtain rfl := ihe he'
      rfl
  | EOptionMatchNone scrut nbody x sbody hscrut hnbody ihscrut ihnbody =>
    cases h₂ with
    | EOptionMatchNone _ _ _ _ _ hnbody' => exact ihnbody hnbody'
    | EOptionMatchSome _ _ _ _ hscrut' _ => exact absurd (ihscrut hscrut') (by simp)
  | EOptionMatchSome scrut nbody x sbody hscrut hsbody ihscrut ihsbody =>
    cases h₂ with
    | EOptionMatchNone _ _ _ _ hscrut' _ => exact absurd (ihscrut hscrut') (by simp)
    | EOptionMatchSome _ _ _ _ hscrut' hsbody' =>
      obtain rfl := Option.some.inj (Value.option.inj (ihscrut hscrut'))
      exact ihsbody hsbody'
  | ENil ty => cases h₂; rfl
  | ECons e₁ e₂ h1 h2 ih1 ih2 =>
    cases h₂ with
    | ECons _ _ h1' h2' =>
      obtain rfl := ih1 h1'
      obtain rfl := Value.list.inj (ih2 h2')
      rfl
  | EListMatchNil scrut nbody hd tl cbody hscrut hnbody ihscrut ihnbody =>
    cases h₂ with
    | EListMatchNil _ _ _ _ _ _ hnbody' => exact ihnbody hnbody'
    | EListMatchCons _ _ _ _ _ hscrut' _ => exact absurd (ihscrut hscrut') (by simp)
  | EListMatchCons scrut nbody hd tl cbody hscrut hcbody ihscrut ihcbody =>
    cases h₂ with
    | EListMatchNil _ _ _ _ _ hscrut' _ => exact absurd (ihscrut hscrut') (by simp)
    | EListMatchCons _ _ _ _ _ hscrut' hcbody' =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj (Value.list.inj (ihscrut hscrut'))
      exact ihcbody hcbody'
  | EListIndex l i hl hi ihl ihi =>
    cases h₂ with
    | EListIndex _ _ hl' hi' =>
      obtain rfl := Value.list.inj (ihl hl')
      obtain rfl := Value.int.inj (ihi hi')
      rfl
  | EListMap e f he hf hlen hat hev ihe ihf ihev =>
    cases h₂ with
    | EListMap _ _ he' hf' hlen' _ hev' =>
      obtain rfl := Value.list.inj (ihe he')
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (ihf hf')
      obtain rfl :=
        List.eq_of_zip_unique hlen hlen'
          fun p hp q hq hpq => ihev p hp (by rw [hpq]; exact hev' q hq)
      rfl
  | EListFlatMap e f he hf hlen hat hev ihe ihf ihev =>
    cases h₂ with
    | EListFlatMap _ _ he' hf' hlen' _ hev' =>
      obtain rfl := Value.list.inj (ihe he')
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (ihf hf')
      obtain rfl :=
        List.eq_of_zip_unique hlen hlen'
          fun p hp q hq hpq => Value.list.inj (ihev p hp (by rw [hpq]; exact hev' q hq))
      rfl
  | EListLength e he ihe =>
    cases h₂ with
    | EListLength _ he' =>
      obtain rfl := Value.list.inj (ihe he')
      rfl
  | EListFindIndexSome e f he hf hatpre hpre hatw hw ihe ihf ihpre ihw =>
    cases h₂ with
    | EListFindIndexSome _ _ he' hf' _ hpre' _ hw' =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (ihf hf')
      exact congrArg (fun n : Nat => Value.option (some (Value.int (n : Int))))
        (List.length_eq_of_append_cons_eq (Value.list.inj (ihe he'))
          (fun hmem => absurd (ihw (hpre' _ hmem)) (by simp))
          (fun hmem => absurd (ihpre _ hmem hw') (by simp)))
    | EListFindIndexNone _ _ he' hf' _ hall' =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (ihf hf')
      obtain rfl := Value.list.inj (ihe he')
      exact absurd (ihw (hall' _ (by simp))) (by simp)
  | EListFindIndexNone e f he hf hat hall ihe ihf ihall =>
    cases h₂ with
    | EListFindIndexSome _ _ he' hf' _ _ _ hw' =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (ihf hf')
      obtain rfl := Value.list.inj (ihe he')
      exact absurd (ihall _ (by simp) hw') (by simp)
    | EListFindIndexNone _ _ _ _ _ _ => rfl
  | EListReverse e he ihe =>
    cases h₂ with
    | EListReverse _ he' =>
      obtain rfl := Value.list.inj (ihe he')
      rfl
  | EListSortOn e f he hf hlen hat hev hcmp ihe ihf ihev =>
    cases h₂ with
    | EListSortOn _ _ he' hf' hlen' _ hev' _ =>
      obtain rfl := Value.list.inj (ihe he')
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (ihf hf')
      obtain rfl :=
        List.eq_of_zip_unique hlen hlen'
          fun p hp q hq hpq => ihev p hp (by rw [hpq]; exact hev' q hq)
      rfl
  | EListSortBy e f he hf hat hev ihe ihf ihev =>
    cases h₂ with
    | EListSortBy _ _ he' hf' _ hev' =>
      obtain rfl := Value.list.inj (ihe he')
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (ihf hf')
      exact congrArg Value.list
        (Value.sortWith_congr fun a ha b hb => Value.bool.inj (ihev a ha b hb (hev' a ha b hb)))
  | EHashmapEmpty kt vt => cases h₂; rfl
  | EHashmapPut m k v hm hk hv herase ihm ihk ihv =>
    cases h₂ with
    | EHashmapPut _ _ _ hm' hk' hv' herase' =>
      obtain rfl := Value.hashmap.inj (ihm hm')
      obtain rfl := ihk hk'
      obtain rfl := ihv hv'
      obtain rfl := Option.some.inj (herase.symm.trans herase')
      rfl
  | EHashmapGet m k hm hk hlookup ihm ihk =>
    cases h₂ with
    | EHashmapGet _ _ hm' hk' hlookup' =>
      obtain rfl := Value.hashmap.inj (ihm hm')
      obtain rfl := ihk hk'
      exact congrArg Value.option (Option.some.inj (hlookup.symm.trans hlookup'))
  | EHashmapMap m f hm hf hkeys hat hev ihm ihf ihev =>
    cases h₂ with
    | EHashmapMap _ _ hm' hf' hkeys' _ hev' =>
      obtain rfl := Value.hashmap.inj (ihm hm')
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Value.closure.inj (ihf hf')
      obtain rfl :=
        List.eq_of_zip_snd_unique (by simpa using congrArg List.length hkeys)
          (hkeys.symm.trans hkeys')
          fun p hp q hq hpq => ihev p hp (by rw [hpq]; exact hev' q hq)
      rfl
  | EHashmapToList m hm ihm =>
    cases h₂ with
    | EHashmapToList _ hm' =>
      obtain rfl := Value.hashmap.inj (ihm hm')
      rfl
  | ETupleNew es hlen hev ihev =>
    cases h₂ with
    | ETupleNew _ hlen' hev' =>
      obtain rfl :=
        List.eq_of_zip_unique hlen hlen'
          fun p hp q hq hpq => ihev p hp (by rw [hpq]; exact hev' q hq)
      rfl
  | ETupleGet e i he hi ihe =>
    cases h₂ with
    | ETupleGet _ _ he' hi' =>
      obtain rfl := Value.tuple.inj (ihe he')
      exact Option.some.inj (hi.symm.trans hi')
