module

public import LgtmDeepLean.Lang.Eval.Yields
public import LgtmDeepLean.Lang.Progress
public import LgtmDeepLean.Lang.Value
public import LgtmDeepLean.Model.Basic.WellFormed
public import LgtmDeepLean.Model.CommentManager.Properties
public import LgtmDeepLean.Model.CommentThreads.Operations
public import LgtmDeepLean.Model.Program

/-! # The order `CommentThreads.toThreadsOrdered` returns threads in

What the shallow model proves of `toThreadsOrdered` by unfolding it, proved here of the calls the
relational semantics says it has: each location's group of threads occurs as a contiguous run of the
result, and within a run the threads are in timestamp order.

Every hypothesis the shallow version did not need is one the deep embedding has to say out loud.
`gs` must declare the names these bodies call, since a `varRef` resolves through the globals table
and nothing says that table is the model's — that is `Model.Declares`, one hypothesis holding both
the struct declarations these proofs read and the lookups they would otherwise list name by name.  And the invariants the shallow
`CommentThreads`
carried as fields of the structure become `CommentManager.WellFormed` and
`CommentThreads.WellFormed`, which is the whole of what makes a thread node's `value` resolve back
to the comment whose timestamp ordered it. -/

@[expose] public section

/-! ## Sortedness

`listIsSortedPredicate` is the shallow model's own predicate, over the `Int`s the DSL's timestamps
are rather than over an arbitrary `Ord`: `Value.cmp?` answers for `int`s with Lean's own `≤` (see
`Value.le?_int`), so that is where the order a sort produced is read. -/

/-- The values are in nondecreasing order: each one is at most everything after it. -/
def listIsSortedPredicate (values : List Int) : Prop :=
  match values with
  | [] => True
  | v :: rest => rest.all (fun other => decide (v ≤ other)) ∧ listIsSortedPredicate rest

theorem listIsSortedPredicate_iff_pairwise (l : List Int) :
    listIsSortedPredicate l ↔ l.Pairwise (· ≤ ·) := by
  induction l with
  | nil => simp [listIsSortedPredicate]
  | cons a l ih => simp [listIsSortedPredicate, ih]

/-- The `Int` a key carries, and a junk answer where it carries none.

Total, because `List.map_mergeSort` needs a function; what the keys really are is `int`s, which is
what `CommentManager.timestampIsInt` supplies, so the junk answer is never reached. -/
private def keyInt (p : Value × Value) : Int :=
  match p.2 with
  | .int i => i
  | _ => 0

/-- The keys a key-sort put in order are in order, given they are all `int`s.

`Value.sortByKey` compares with `Value.le?`, which is neither transitive nor total over values at
large — two values of types with no ordering between them are a pair it has no answer for — so the
comparison is carried over to the `Int`s the keys hold, where both hold.  `List.map_mergeSort` is
the carrying over: the two comparisons agree on the pairs this sort asks about, which is all a sort
depends on. -/
private theorem pairwise_keyInt_sortByKey {vks : List (Value × Value)}
    (hint : ∀ p ∈ vks, ∃ i : Int, p.2 = .int i) :
    ((Value.sortByKey vks).map keyInt).Pairwise (· ≤ ·) := by
  have hagree : ∀ a ∈ vks, ∀ b ∈ vks,
      (Value.le? a.2 b.2 == some true) = decide (keyInt a ≤ keyInt b) := by
    intro a ha b hb
    obtain ⟨i, hi⟩ := hint a ha
    obtain ⟨j, hj⟩ := hint b hb
    simp [keyInt, hi, hj]
  rw [Value.sortByKey, List.map_mergeSort (s := fun a b => decide (a ≤ b)) hagree]
  have := List.pairwise_mergeSort (le := fun a b : Int => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (vks.map keyInt)
  simpa using this

/-! ## Helpers over lists

The facts about lists this development needs that the library states the other way round. -/

/-- A list with an element the predicate accepts splits at the *first* such element: everything
before it is turned down, and it is accepted.

What `Eval.EListFindIndexSome` asks for, which is the search's short circuit read as a fact about
the list — `pre ++ w :: post` with `pre` all turned down is the whole of what makes `pre.length` the
index found.  Classical, since nothing is assumed decidable: the split exists, and which element it
is at is not computed here. -/
theorem exists_first_of_mem {α : Type} {l : List α} (P : α → Prop) {x : α} (hx : x ∈ l)
    (hP : P x) : ∃ pre w post, l = pre ++ w :: post ∧ (∀ u ∈ pre, ¬P u) ∧ P w := by
  classical
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    by_cases hPa : P a
    · exact ⟨[], a, l, rfl, by simp, hPa⟩
    · rcases List.mem_cons.mp hx with rfl | hx'
      · exact absurd hP hPa
      · obtain ⟨pre, w, post, rfl, hpre, hw⟩ := ih hx'
        refine ⟨a :: pre, w, post, by simp, fun u hu => ?_, hw⟩
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact hPa
        · exact hpre u hu'

/-- A list that is one of the pieces being run together is a contiguous run of the result. -/
private theorem infix_flatten_of_mem {α : Type} {l : List α} {ls : List (List α)} (h : l ∈ ls) :
    l <:+: ls.flatten := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem h
  exact ⟨s.flatten, t.flatten, by simp⟩

/-- An element of either of two lists of the same length is half of one of the pairs their zip
carries: the converse of `List.of_mem_zip`, which is what reads a premise stated over a zip — as
every `Eval` rule that calls a function per element states its own — at one particular element. -/
theorem exists_mem_zip_of_mem_left {α β : Type} {as : List α} {bs : List β}
    (hlen : as.length = bs.length) {a : α} (ha : a ∈ as) : ∃ b, (a, b) ∈ as.zip bs := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  have hi' : i < bs.length := by omega
  exact ⟨bs[i], List.mem_zip_of_getElem? (List.getElem?_eq_getElem hi)
    (List.getElem?_eq_getElem hi')⟩

theorem exists_mem_zip_of_mem_right {α β : Type} {as : List α} {bs : List β}
    (hlen : as.length = bs.length) {b : β} (hb : b ∈ bs) : ∃ a, (a, b) ∈ as.zip bs := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
  have hi' : i < as.length := by omega
  exact ⟨as[i], List.mem_zip_of_getElem? (List.getElem?_eq_getElem hi')
    (List.getElem?_eq_getElem hi)⟩

/-- A pointwise existential over a list is a list of witnesses: the converse of what every `Eval`
rule that calls a function per element demands, which is a premise over a zip rather than one
answer per element.  Building the zip's second half is what a forward proof needs and an inversion
proof never does — inverting one of those rules is handed the zip already, where constructing a
derivation of one has to produce it from one witness per element of the list being walked. -/
theorem exists_zip_of_forall_exists {α β : Type} {l : List α} {P : α → β → Prop}
    (h : ∀ x ∈ l, ∃ y, P x y) : ∃ ys, l.length = ys.length ∧ ∀ p ∈ l.zip ys, P p.1 p.2 := by
  induction l with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := h x (by simp)
    obtain ⟨ys, hlen, hall⟩ := ih fun x' hx' => h x' (by simp [hx'])
    refine ⟨y :: ys, by simpa using hlen, fun p hp => ?_⟩
    rcases (by simpa using hp : p = (x, y) ∨ p ∈ xs.zip ys) with rfl | hp'
    · exact hy
    · exact hall p hp'


/-! ## Comparing two comment refs

What `==` answers when the two sides are `CommentRef`s, which is the one comparison the
declarations below actually run and the one place a theorem here reads a declaration to the bottom
rather than reading a field off a value.

`Value.beq?` is partial, and `Ty.comparable` — the type checker's side of it — is not enough to say
it answers: nothing in this development derives totality of the comparison from comparability of the
type, and `Progress.lean`'s module docstring says why it is still open in general.  What makes it
answerable *here* is that `CommentRef`'s whole content is one `string` field, so a value typed as
one has exactly one shape and the comparison is a finite computation with no appeal to
`TypeDecls.budget`. -/

/-- A value typed as a `CommentRef` is one field holding one string.

Canonical forms taken all the way down, where `Value.eq_struct_of_hasType` stops at the struct: the
names clause of `Value.HasType` is a permutation of the declaration's names, so a `CommentRef`
value carries the declaration's one field and no second binding of it, and the typing clause then
says what that field holds.  The second binding is exactly what used to be possible, and what made
`Value.beq?` give up on a pair of well-typed values. -/
private theorem CommentRef.eq_of_hasType {td : TypeDecls} {v : Value}
    (hd : td.ss.lookup "CommentRef" = some CommentRef)
    (hv : v.HasType td (.struct "CommentRef")) :
    ∃ s : String, v = .struct "CommentRef" [("id", .string s)] := by
  obtain ⟨fvs, rfl⟩ := Value.eq_struct_of_hasType hv
  obtain ⟨sd, hsd, hnames, htys, -⟩ := Value.hasType_struct_iff.mp hv
  clear hv
  obtain rfl : sd = CommentRef := Option.some.inj (hsd.symm.trans hd)
  have hfst : fvs.map Prod.fst = ["id"] := List.perm_singleton.mp hnames
  obtain ⟨⟨f, w⟩, rfl⟩ := List.length_eq_one_iff.mp (by simpa using congrArg List.length hfst)
  obtain rfl : f = "id" := by simpa using hfst
  obtain ⟨s, rfl⟩ := Value.hasType_string_iff.mp (htys "id" .string w rfl rfl)
  exact ⟨s, rfl⟩

/-- So comparing two of them has an answer, and the answer is whether they are the same value.

All three uses are read off this one statement: the answer exists at all, which is what rules out
`Stuck.equalsIncomparable`; it is `true` at a ref compared with itself, which is what makes a search
find the selected ref; and it is `false` at a ref that is not it, which is what makes the search
pass over the refs before it. -/
theorem CommentRef.beq?_eq_some {td : TypeDecls} {a b : Value}
    (hd : td.ss.lookup "CommentRef" = some CommentRef)
    (ha : a.HasType td (.struct "CommentRef")) (hb : b.HasType td (.struct "CommentRef")) :
    ∃ x, Value.beq? a b = some x ∧ (x = true ↔ a = b) := by
  obtain ⟨s, rfl⟩ := CommentRef.eq_of_hasType hd ha
  obtain ⟨t, rfl⟩ := CommentRef.eq_of_hasType hd hb
  refine ⟨s == t, by simp [Value.beq?, Value.beqFields?, FieldValues.extract?], ?_⟩
  simp

/-! ## Every location's threads

`asAlist` reads each location's root comments out of the manager, hands the list to
`sortThreadLists`, and sorts what comes back by location.  The sort by location rearranges and
nothing else, so every group in the result is one of those `sortThreadLists` answers — which is what
makes the sortedness within a group a fact about `sortThreadLists` alone. -/

theorem CommentThreads.asAlist.sortThreadLists_apply_of_mem {td : TypeDecls} {gs : Globals}
    {threads manager : Value} {groups : List Value}
    (hDeclares : Model.Declares td gs)
    (h : CommentThreads.asAlist.Apply td gs [threads, manager] (.list groups)) :
    ∀ group ∈ groups, ∃ loc roots, CommentManager.ContainsComments manager roots ∧
      CommentThreads.asAlist.sortThreadLists.Apply td gs
        [threads, manager, .tuple [loc, .list roots]] group := by
  obtain ⟨-, -, hbody⟩ := h
  obtain ⟨refToComment, hrefLam, hbody⟩ := Eval.let_inv hbody
  obtain ⟨lookupCommentForRef, hlookupLam, hbody⟩ := Eval.let_inv hbody
  obtain ⟨locatedRootComments, hlrc, hbody⟩ := Eval.let_inv hbody
  obtain ⟨sortAtLocation, hsortLam, hbody⟩ := Eval.let_inv hbody
  obtain ⟨threadsSorted, htsl, hbody⟩ := Eval.let_inv hbody
  obtain rfl := Eval.lam_inv hrefLam
  obtain rfl := Eval.lam_inv hlookupLam
  obtain rfl := Eval.lam_inv hsortLam
  -- The sort by location rearranges and nothing else, so a group is one of the calls' answers.
  obtain ⟨lts, cmp, hlts, hgroups⟩ := Eval.listSortBy_inv hbody
  have hltsv := Eval.varRef_inv hlts
  lgtm_env at hltsv
  subst hltsv
  obtain rfl : groups = Value.sortWith cmp lts := by simpa using hgroups
  -- The threads at each location are what the call to `sortThreadLists` returned.
  obtain ⟨lrc, lts', _cb, _cg, _ps, _body, hlrcv, hsortFn, hslen, hsev, hlts'⟩ :=
    Eval.listMap_inv htsl
  obtain rfl : lts = lts' := by simpa using hlts'
  have hlrcvv := Eval.varRef_inv hlrcv
  have hsortFnv := Eval.varRef_inv hsortFn
  lgtm_env at hlrcvv hsortFnv
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hsortFnv
  subst hlrcvv
  -- Each of those lists of root comments was read out of the manager.
  obtain ⟨entries, lrc', _cb, _cg, _ps, _body, hentries, hlookupFn, helen, hlev, hlrc'⟩ :=
    Eval.listMap_inv hlrc
  obtain rfl : lrc = lrc' := by simpa using hlrc'
  have hlookupFnv := Eval.varRef_inv hlookupFn
  lgtm_env at hlookupFnv
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hlookupFnv
  have hcomments : ∀ p ∈ entries.zip lrc, ∃ loc roots, p.2 = .tuple [loc, .list roots] ∧
      CommentManager.ContainsComments manager roots := by
    intro p hp
    obtain ⟨locv, hlocv, hentry⟩ := Eval.let_inv (hlev p hp)
    obtain ⟨atLoc, hatLoc, hentry⟩ := Eval.let_inv hentry
    obtain ⟨comments, hmapComments, hentry⟩ := Eval.let_inv hentry
    -- the comments at this location, one per ref, each read out of the manager
    obtain ⟨refs, cs, _cb, _cg, _ps, _body, hrefs, hcFn, hclen, hcev, rfl⟩ :=
      Eval.listMap_inv hmapComments
    have hcFnv := Eval.varRef_inv hcFn
    lgtm_env at hcFnv
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hcFnv
    have hmanagerComments : CommentManager.ContainsComments manager cs := by
      intro c hc
      obtain ⟨ref, hpair⟩ := exists_mem_zip_of_mem_right hclen hc
      obtain ⟨w, hcall, hbound⟩ := Eval.optionMatch_unreachable_inv (hcev _ hpair)
      have hw := Eval.varRef_inv hbound
      lgtm_env at hw
      subst hw
      obtain ⟨vs, hvlen, hvev, happly⟩ :=
        FuncDecl.apply_of_eval_app
          (by lgtm_env [CommentThreads.asAlist] using hDeclares.get)
          (by lgtm_env [CommentThreads.asAlist]) hcall
      obtain rfl : vs = [manager, ref] := Eval.Yields.eq_of_args hvev hvlen
        (.cons (.varRef (by lgtm_env [CommentThreads.asAlist]))
          (.cons (.varRef (by lgtm_env [CommentThreads.asAlist])) .nil))
      exact ⟨ref, CommentManager.get.eq_get? happly⟩
    -- and the pair this location contributes is that location beside them
    obtain ⟨tvs, htvs, htlen, htev⟩ := Eval.tupleNew_inv hentry
    obtain rfl : tvs = [locv, .list cs] := Eval.Yields.eq_of_args htev htlen
      (.cons (.varRef (by lgtm_env)) (.cons (.varRef (by lgtm_env)) .nil))
    exact ⟨locv, cs, htvs, hmanagerComments⟩
  -- Putting the two together: the group, the location it is at, and the comments it came from.
  intro group hgroup
  obtain ⟨entry, hpair⟩ :=
    exists_mem_zip_of_mem_right hslen (Value.mem_sortWith.mp hgroup)
  obtain ⟨locatedThreads, hlpair⟩ := exists_mem_zip_of_mem_right helen (List.of_mem_zip hpair).1
  obtain ⟨loc, roots, rfl, hroots⟩ := hcomments _ hlpair
  obtain ⟨vs, hvlen, hvev, happly⟩ :=
    FuncDecl.apply_of_eval_app
      (by lgtm_env [CommentThreads.asAlist] using hDeclares.sortThreadLists)
      (by lgtm_env [CommentThreads.asAlist]) (hsev _ hpair)
  obtain rfl : vs = [threads, manager, .tuple [loc, .list roots]] :=
    Eval.Yields.eq_of_args hvev hvlen
      (.cons (.varRef (by lgtm_env [CommentThreads.asAlist]))
        (.cons (.varRef (by lgtm_env [CommentThreads.asAlist]))
          (.cons (.varRef (by lgtm_env [CommentThreads.asAlist])) .nil)))
  exact ⟨loc, roots, hroots, by lgtm_env [CommentThreads.asAlist] using happly⟩


/-! ## One location's threads

`sortThreadLists` is where the order comes from: it sorts a location's root comments by timestamp
and then replaces each comment by the thread node its ref resolves to.  So the threads it hands back
are in the order the comments' timestamps put them in, which is what this says — the timestamps
being the ones `manager` records, which is where both well-formedness hypotheses are spent: the one
on `threads` is what gets from a node back to the ref it is bound to, and the one on `manager` is
what gets from that ref back to the comment the key was read off. -/

theorem CommentThreads.asAlist.sortThreadLists.isSortedByTimestamp {td : TypeDecls} {gs : Globals}
    {threads manager loc : Value} {roots : List Value} {result : Value}
    (hDeclares : Model.DeclaresTypes td)
    (hThreadsWF : CommentThreads.WellFormed td threads)
    (hManagerWF : CommentManager.WellFormed td manager)
    (hroots : CommentManager.ContainsComments manager roots)
    (h : CommentThreads.asAlist.sortThreadLists.Apply td gs
      [threads, manager, .tuple [loc, .list roots]] result) :
    ∃ ts stamps, result = .tuple [loc, .list ts] ∧ ts.length = stamps.length ∧
      (∀ p ∈ ts.zip stamps, CommentManager.rootTimestamp? manager p.1 = some p.2) ∧
      listIsSortedPredicate stamps := by
  obtain ⟨-, -, hbody⟩ := h
  obtain ⟨sortedRoots, hsort, hbody⟩ := Eval.let_inv hbody
  obtain ⟨lookupFn, hlookupFn, hbody⟩ := Eval.let_inv hbody
  obtain ⟨sortedThreads, hmap, hbody⟩ := Eval.let_inv hbody
  -- The list being sorted is the location's root comments.
  obtain ⟨vs, ks, _cb, _cg, _ps, _keyBody, hlist, hfun, hklen, hkeys, rfl⟩ :=
    Eval.listSortOn_inv hsort
  obtain ⟨tvs, hscrut, hget⟩ := Eval.tupleGet_inv hlist
  have htvs := Eval.varRef_inv hscrut
  lgtm_env [CommentThreads.asAlist.sortThreadLists] at htvs
  subst htvs
  obtain rfl : roots = vs := by simpa using hget
  -- Each key is the timestamp its comment records, so each key is an `int`.
  obtain ⟨rfl, rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ ∧ _ := by
    lgtm_env [Value.closure.injEq] using Eval.lam_inv hfun
  have hkeyField : ∀ p ∈ roots.zip ks, p.1.field? "createdTimestamp" = some p.2 := by
    intro p hp
    obtain ⟨_n, _fvs, hc, hf⟩ := Eval.structGet_inv (hkeys p hp)
    have hlc := Eval.varRef_inv hc
    lgtm_env at hlc
    rw [hlc]
    simpa [Value.field?] using hf
  have hkeyInt : ∀ p ∈ roots.zip ks, ∃ i : Int, p.2 = .int i := by
    intro p hp
    obtain ⟨ref, href⟩ := hroots p.1 (List.of_mem_zip hp).1
    obtain ⟨i, hi⟩ := CommentManager.timestampIsInt hDeclares hManagerWF href
    exact ⟨i, by simpa using (hkeyField p hp).symm.trans hi⟩
  -- Each sorted comment was replaced by the node its ref resolves to.
  obtain ⟨sr, ts, _cb, _cg, _ps, _mapBody, hsr, hfn, hmlen, hmev, rfl⟩ := Eval.listMap_inv hmap
  obtain rfl := Eval.lam_inv hlookupFn
  have hsrv := Eval.varRef_inv hsr
  have hfnv := Eval.varRef_inv hfn
  lgtm_env [CommentThreads.asAlist.sortThreadLists] at hsrv hfnv
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hfnv
  subst hsrv
  have hnode : ∀ p ∈ ((Value.sortByKey (roots.zip ks)).map Prod.fst).zip ts,
      ∃ ref, p.1.field? "ref" = some ref ∧ CommentThreads.node? threads ref = some p.2 := by
    intro p hp
    obtain ⟨node, hscrut, hthread⟩ := Eval.optionMatch_unreachable_inv (hmev p hp)
    obtain ⟨kvs, ref, hm, hk, hlookup⟩ := Eval.hashmapGet_inv hscrut
    obtain ⟨_tn, _tfvs, ht, hcn⟩ := Eval.structGet_inv hm
    obtain ⟨_cn, _cfvs, hc, hcr⟩ := Eval.structGet_inv hk
    have hlt := Eval.varRef_inv ht
    have hlc := Eval.varRef_inv hc
    have hlth := Eval.varRef_inv hthread
    lgtm_env at hlt hlc hlth
    subst hlt
    subst hlth
    exact ⟨ref, by rw [hlc]; simpa [Value.field?] using hcr,
      by simp [CommentThreads.node?, Value.lookupField?, Value.field?, hcn, hlookup]⟩
  -- What comes back is the location beside those threads.
  obtain ⟨rvs, rfl, hrlen, hrev⟩ := Eval.tupleNew_inv hbody
  obtain ⟨a, b, rfl⟩ := List.length_eq_two_iff.mp (by simpa using hrlen.symm)
  obtain ⟨_rtvs, hloc, hloci⟩ :=
    Eval.tupleGet_inv (hrev ((Expression.varRef "commentThreadRoots").tupleGet 0, a) (by simp))
  have hlocv := Eval.varRef_inv hloc
  have hthreadsv := Eval.varRef_inv (hrev (Expression.varRef "sortedThreads", b) (by simp))
  lgtm_env [CommentThreads.asAlist.sortThreadLists] at hlocv hthreadsv
  subst hlocv
  subst hthreadsv
  obtain rfl : a = loc := by simpa using hloci.symm
  -- The threads are as many as the sorted pairs, and the key of each pair is its thread's timestamp.
  refine ⟨ts, (Value.sortByKey (roots.zip ks)).map keyInt, rfl, by simpa using hmlen.symm,
    fun p hp => ?_, (listIsSortedPredicate_iff_pairwise _).mpr (pairwise_keyInt_sortByKey hkeyInt)⟩
  obtain ⟨thread, stamp⟩ := p
  obtain ⟨i, hpi⟩ := List.mem_iff_getElem?.mp hp
  obtain ⟨hti, hsi⟩ := List.getElem?_zip_eq_some.mp hpi
  obtain ⟨c, key, hq, rfl⟩ : ∃ c key, (Value.sortByKey (roots.zip ks))[i]? = some (c, key) ∧
      keyInt (c, key) = stamp := by simpa using hsi
  obtain ⟨ref, href, hnoderef⟩ := hnode (c, thread) (List.mem_zip_of_getElem? (by simp [hq]) hti)
  -- The node names the ref it is bound to, and that ref names the comment the key was read off.
  have hmem : (c, key) ∈ roots.zip ks := Value.mem_sortByKey.mp (List.mem_of_getElem? hq)
  have hget : CommentManager.get? manager ref = some c := by
    obtain ⟨ref', href'⟩ := hroots c (List.of_mem_zip hmem).1
    obtain rfl : ref' = ref := by
      simpa [href] using (hManagerWF.refMatchesKey ref' c href').symm
    exact href'
  obtain ⟨i', hi'⟩ := CommentManager.timestampIsInt hDeclares hManagerWF hget
  obtain rfl : key = .int i' := by simpa using (hkeyField (c, key) hmem).symm.trans hi'
  simp [CommentManager.rootTimestamp?, hThreadsWF.rootMatchesKey ref thread hnoderef, hget, hi',
    keyInt]

/-- Every group `asAlist` produces is a location's threads in timestamp order: the two halves above
put together, one for where a group comes from and one for the order it is in. -/
theorem CommentThreads.asAlist.threadLocationsSortedByTimestamp {td : TypeDecls} {gs : Globals}
    {threads manager : Value} {groups : List Value}
    (hDeclares : Model.Declares td gs)
    (hThreadsWF : CommentThreads.WellFormed td threads)
    (hManagerWF : CommentManager.WellFormed td manager)
    (h : CommentThreads.asAlist.Apply td gs [threads, manager] (.list groups)) :
    ∀ group ∈ groups, ∃ loc ts stamps, group = .tuple [loc, .list ts] ∧
      ts.length = stamps.length ∧
      (∀ p ∈ ts.zip stamps, CommentManager.rootTimestamp? manager p.1 = some p.2) ∧
      listIsSortedPredicate stamps := by
  intro group hgroup
  obtain ⟨loc, roots, hroots, happly⟩ :=
    CommentThreads.asAlist.sortThreadLists_apply_of_mem hDeclares h group hgroup
  obtain ⟨ts, stamps, hgeq, hlen, hstamps, hsorted⟩ :=
    CommentThreads.asAlist.sortThreadLists.isSortedByTimestamp hDeclares.toDeclaresTypes
      hThreadsWF hManagerWF
      hroots happly
  exact ⟨loc, ts, stamps, hgeq, hlen, hstamps, hsorted⟩

/-! ## The whole list

`toThreadsOrdered` runs the groups together, so each group's list of threads is a contiguous run of
the result and keeps the order `sortThreadLists` gave it.  This is the statement the shallow model
proves by unfolding `asAlist`; here the `asAlist` the flatten ran over is what the existential hands
back, since nothing says two calls to it under the same arguments produce the same value — that
would be determinacy of `Eval`, which this development does not have and does not need. -/

theorem CommentThreads.toThreadsOrdered.groupsAreSorted {td : TypeDecls} {gs : Globals}
    {threads manager : Value} {ordered : List Value}
    (hDeclares : Model.Declares td gs)
    (hThreadsWF : CommentThreads.WellFormed td threads)
    (hManagerWF : CommentManager.WellFormed td manager)
    (h : CommentThreads.toThreadsOrdered.Apply td gs [threads, manager] (.list ordered)) :
    ∃ groups, CommentThreads.asAlist.Apply td gs [threads, manager] (.list groups) ∧
      ∀ group ∈ groups, ∃ loc ts stamps, group = .tuple [loc, .list ts] ∧
        ts.IsInfix ordered ∧ ts.length = stamps.length ∧
        (∀ p ∈ ts.zip stamps, CommentManager.rootTimestamp? manager p.1 = some p.2) ∧
        listIsSortedPredicate stamps := by
  obtain ⟨-, -, hbody⟩ := h
  obtain ⟨groups, tss, _cb, _cg, _ps, _body, hcall, hfn, hflen, hfev, hres⟩ :=
    Eval.listFlatMap_inv hbody
  obtain ⟨rfl, rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ ∧ _ := by
    lgtm_env [Value.closure.injEq] using Eval.lam_inv hfn
  obtain rfl : ordered = tss.flatten := by simpa using hres
  -- The groups are what the call to `asAlist` returned.
  obtain ⟨vs, hvlen, hvev, happly⟩ :=
    FuncDecl.apply_of_eval_app
      (by lgtm_env [CommentThreads.toThreadsOrdered] using hDeclares.asAlist)
      (by lgtm_env [CommentThreads.toThreadsOrdered]) hcall
  obtain rfl : vs = [threads, manager] := Eval.Yields.eq_of_args hvev hvlen
    (.cons (.varRef (by lgtm_env [CommentThreads.toThreadsOrdered]))
      (.cons (.varRef (by lgtm_env [CommentThreads.toThreadsOrdered])) .nil))
  lgtm_env at happly
  refine ⟨groups, happly, fun group hgroup => ?_⟩
  obtain ⟨loc, ts, stamps, rfl, hlen, hstamps, hsorted⟩ :=
    CommentThreads.asAlist.threadLocationsSortedByTimestamp hDeclares
      hThreadsWF hManagerWF happly group hgroup
  -- And the group's own threads are one of the lists being run together.
  obtain ⟨l, hpair⟩ := exists_mem_zip_of_mem_left hflen hgroup
  obtain ⟨tvs, hscrut, hidx⟩ := Eval.tupleGet_inv (hfev _ hpair)
  have htvs := Eval.varRef_inv hscrut
  lgtm_env at htvs
  subst htvs
  obtain rfl : ts = l := by simpa using hidx
  exact ⟨loc, ts, stamps, rfl, infix_flatten_of_mem (List.of_mem_zip hpair).2, hlen, hstamps,
    hsorted⟩

/-! ## The model's own table

`Model.Declares` above is a condition on the two tables, and `modelProgram` meets it by `rfl` in
every clause: the model declares each of those names under its own name.  So this is the
theorem read as a fact about the model rather than about any table that happens to declare the right
things, and it is what says that hypothesis is not vacuous. -/

theorem CommentThreads.toThreadsOrdered.groupsAreSorted_modelProgram {threads manager : Value}
    {ordered : List Value}
    (hThreadsWF : CommentThreads.WellFormed modelProgram.typeDecls threads)
    (hManagerWF : CommentManager.WellFormed modelProgram.typeDecls manager)
    (h : modelProgram.Apply "CommentThreads.toThreadsOrdered" [threads, manager] (.list ordered)) :
    ∃ groups,
      CommentThreads.asAlist.Apply modelProgram.typeDecls modelProgram.globals [threads, manager]
        (.list groups) ∧
      ∀ group ∈ groups, ∃ loc ts stamps, group = .tuple [loc, .list ts] ∧
        ts.IsInfix ordered ∧ ts.length = stamps.length ∧
        (∀ p ∈ ts.zip stamps, CommentManager.rootTimestamp? manager p.1 = some p.2) ∧
        listIsSortedPredicate stamps := by
  obtain ⟨d, hd, happly⟩ := h
  obtain rfl : CommentThreads.toThreadsOrdered = d := by
    simpa using (show modelProgram.lookup "CommentThreads.toThreadsOrdered" =
      some CommentThreads.toThreadsOrdered from rfl).symm.trans hd
  exact CommentThreads.toThreadsOrdered.groupsAreSorted Model.declares_modelProgram
    hThreadsWF hManagerWF happly

/-- `ref` names a comment of the thread rooted at `thread`. -/
inductive CommentThread.HasRef (threads : Value) : Value → Value → Prop where
  | root {thread ref : Value} :
    thread.field? "value" = some ref → CommentThread.HasRef threads thread ref
  | child {thread childRef childNode ref : Value} {childRefs : List Value} :
    thread.field? "children" = some (.list childRefs) → childRef ∈ childRefs →
    CommentThreads.node? threads childRef = some childNode →
    CommentThread.HasRef threads childNode ref →
    CommentThread.HasRef threads thread ref

/-- One call to `linearize` taken apart: the list it returns holds the comment the manager has
under the ref the node names, and one run per child, each the answer to a call on that child's
node.

The children are reached through the sort, which rearranges and nothing else —
`Value.mem_sortWith` is the step — so nothing here is said about the order the runs come in. -/
theorem CommentThread.linearize.apply_inv {td : TypeDecls} {gs : Globals}
    {threads manager thread : Value} {comments : List Value}
    (hDeclares : Model.Declares td gs)
    (h : CommentThread.linearize.Apply td gs
      [threads, manager, thread] (.list comments)) :
    ∃ root c childRefs, thread.field? "value" = some root ∧
      CommentManager.get? manager root = some c ∧ c ∈ comments ∧
      thread.field? "children" = some (.list childRefs) ∧
      ∀ r ∈ childRefs, ∃ node cs, CommentThreads.node? threads r = some node ∧
        CommentThread.linearize.Apply td gs
          [threads, manager, node] (.list cs) ∧ ∀ x ∈ cs, x ∈ comments := by
  obtain ⟨-, -, hbody⟩ := h
  obtain ⟨expectComment, hexpectLam, hbody⟩ := Eval.let_inv hbody
  obtain ⟨comparisonFunction, hcmpLam, hbody⟩ := Eval.let_inv hbody
  obtain ⟨sortedChildren, hsort, hbody⟩ := Eval.let_inv hbody
  obtain rfl := Eval.lam_inv hexpectLam
  obtain rfl := Eval.lam_inv hcmpLam
  cases hbody with
  | ECons _ _ hhead htail =>
    -- The head of the list is the thread's own comment, read out of the manager.
    cases hhead with
    | @EApp _env _cb _cg _ps _lbody argVals v _ _ hf hlen hargs _ hcbody =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ ∧ _ := by
        lgtm_env [Value.closure.injEq] using Eval.varRef_inv hf
      obtain ⟨root, rfl⟩ := List.length_eq_one_iff.mp (by simpa using hlen.symm)
      obtain ⟨_tn, _tfvs, hthreadRef, hvalue⟩ :=
        Eval.structGet_inv
          (hargs ((Expression.varRef "thread").structGet "value", root) (by simp))
      have hthreadEq := Eval.varRef_inv hthreadRef
      lgtm_env [CommentThread.linearize] at hthreadEq
      have hrootField : thread.field? "value" = some root := by
        rw [hthreadEq]; simpa [Value.field?] using hvalue
      -- The comment that ref names is the one the manager has under it.
      obtain ⟨c, hcall, hbound⟩ := Eval.optionMatch_unreachable_inv hcbody
      have hcv := Eval.varRef_inv hbound
      lgtm_env at hcv
      subst hcv
      obtain ⟨vs, hvlen, hvev, hgetApply⟩ :=
        FuncDecl.apply_of_eval_app
          (by lgtm_env [CommentThread.linearize] using hDeclares.get)
          (by lgtm_env [CommentThread.linearize]) hcall
      obtain rfl : vs = [manager, root] := Eval.Yields.eq_of_args hvev hvlen
        (.cons (.varRef (by lgtm_env [CommentThread.linearize]))
          (.cons (.varRef (by lgtm_env [CommentThread.linearize])) .nil))
      -- The rest of the list is one run per child, each the list that child's own call returned.
      obtain ⟨refs, lists, _fcb, _fcg, _fps, _fbody, hrefs, hfn, hflen, hfev, hlists⟩ :=
        Eval.listFlatMap_inv htail
      simp only [Value.list.injEq] at hlists
      subst hlists
      have hrefsv := Eval.varRef_inv hrefs
      lgtm_env at hrefsv
      obtain ⟨childRefs, cmp, hchildren, hsorted⟩ := Eval.listSortBy_inv hsort
      subst hrefsv
      obtain rfl : refs = Value.sortWith cmp childRefs := by simpa using hsorted
      obtain ⟨_cn, _cfvs, hthreadRef', hchildField⟩ := Eval.structGet_inv hchildren
      have hthreadEq' := Eval.varRef_inv hthreadRef'
      lgtm_env [CommentThread.linearize] at hthreadEq'
      obtain ⟨rfl, rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ ∧ _ := by
        lgtm_env [Value.closure.injEq] using Eval.lam_inv hfn
      refine ⟨root, c, childRefs, hrootField, CommentManager.get.eq_get? hgetApply, by simp,
        by rw [hthreadEq']; simpa [Value.field?] using hchildField, fun r hr => ?_⟩
      -- The child is one of the refs the flattening ran over, so one of the runs is its own.
      obtain ⟨cs, hpair⟩ := exists_mem_zip_of_mem_left hflen (Value.mem_sortWith.mpr hr)
      obtain ⟨node, hscrut, hreccall⟩ := Eval.optionMatch_unreachable_inv (hfev _ hpair)
      obtain ⟨kvs, vk, hm, hk, hlookup⟩ := Eval.hashmapGet_inv hscrut
      obtain ⟨_nn, _nfvs, hthreadsRef, hnodes⟩ := Eval.structGet_inv hm
      have hthreadsEq := Eval.varRef_inv hthreadsRef
      have hvk := Eval.varRef_inv hk
      lgtm_env [CommentThread.linearize] at hthreadsEq hvk
      subst hvk
      have hnode : CommentThreads.node? threads r = some node := by
        rw [hthreadsEq]
        simp [CommentThreads.node?, Value.lookupField?, Value.field?, hnodes, hlookup]
      -- And that run is what the recursive call on the child's node returned.
      obtain ⟨rvs, hrvlen, hrvev, hrapply⟩ :=
        FuncDecl.apply_of_eval_app
          (by lgtm_env [CommentThread.linearize] using hDeclares.linearize)
          (by lgtm_env [CommentThread.linearize]) hreccall
      obtain rfl : rvs = [threads, manager, node] := Eval.Yields.eq_of_args hrvev hrvlen
        (.cons (.varRef (by lgtm_env [CommentThread.linearize]))
          (.cons (.varRef (by lgtm_env [CommentThread.linearize]))
            (.cons (.varRef (by lgtm_env [CommentThread.linearize])) .nil)))
      exact ⟨node, cs, hnode, hrapply, fun x hx =>
        List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨cs, (List.of_mem_zip hpair).2, hx⟩)⟩

/-! ## Existence: a call to `linearize` on a registered, well-founded thread pool returns

Everything above inverts an `Eval` that is assumed to exist; what follows builds one.  The fuel
parameter `linearizeRecWithFuel` carried used to make a call total no matter what
`commentTreeNodes` held; `linearize` instead asks `CommentThreads.WellFormed` for the two facts
fuel stood in for — `childrenRegistered`, so the recursion never meets a dangling ref, and
`childEdgeWf`, so it never meets a cycle — and this is where that trade is cashed in. -/

/-- The order `linearize`'s sort puts two child refs in: the manager's timestamp order, with a
junk `false` answer on a ref the manager does not cover.

Total, because `Eval.EListSortBy` needs a `Value → Value → Bool`; what two refs' created timestamps
really are is `Int`s as long as the manager covers both, which is what `CommentThreads.NodesCovered`
supplies at every pair this sort asks about, so the junk answer is never reached. -/
private def refLe (manager a b : Value) : Bool :=
  match (CommentManager.get? manager a).bind (fun c => c.field? "createdTimestamp"),
      (CommentManager.get? manager b).bind (fun c => c.field? "createdTimestamp") with
  | some (.int i), some (.int j) => decide (i ≤ j)
  | _, _ => false

/-- `refLe` read off the timestamps directly, once both refs are known to resolve to comments with
`int` timestamps: the match in its definition is then forced down its one live branch. -/
private theorem refLe_eq_decide {manager a b ca cb : Value} {i j : Int}
    (ha : CommentManager.get? manager a = some ca)
    (hi : ca.field? "createdTimestamp" = some (.int i))
    (hb : CommentManager.get? manager b = some cb)
    (hj : cb.field? "createdTimestamp" = some (.int j)) :
    refLe manager a b = decide (i ≤ j) := by
  simp [refLe, ha, hb, hi, hj]

/-- A call to `expectComment` — the closure `linearize` lets over the manager it was called
with — at a ref the manager covers.  Every site that calls it (the head of the list, each pair the
sort compares, and nowhere else) differs only in the caller's own environment and in the expression
that produced `ref`, which is what `callerEnv` and `argE` abstract over; the closure itself, and so
the body this runs, is the same wherever it is called from. -/
private theorem CommentThread.linearize.apply_expectComment {td : TypeDecls} {gs : Globals}
    {threads manager thread : Value} {callerEnv : Env} {argE : Expression} {ref ca : Value}
    (hGet : gs.lookup "CommentManager.get" = some CommentManager.get)
    (hManager : manager.HasType td (.struct "CommentManager"))
    (hrefHasType : ref.HasType td (.struct "CommentRef"))
    (hcGet : CommentManager.get? manager ref = some ca)
    (hcallerLookup : callerEnv.lookup "expectComment" =
      some ((CommentThread.linearize.callEnv gs [threads, manager, thread]).closure
        [("ref", Ty.struct "CommentRef")]
        (.optionMatch (.app (.varRef "CommentManager.get") [.varRef "manager", .varRef "ref"])
          (.unreachable (.struct "Comment") "Comments are required to be present in the manager")
          "c" (.varRef "c"))))
    (hargE : Eval.Yields td callerEnv argE ref) :
    Eval.Yields td callerEnv (.app (.varRef "expectComment") [argE]) ca := by
  refine Eval.Yields.app_closure hcallerLookup (.cons hargE .nil) (.cons "ref" hrefHasType .nil) ?_
  exact .optionMatch_some
    (.app_global hGet (by yields_lookup)
      (.cons (.varRef (by yields_lookup)) (.cons (.varRef (by yields_lookup)) .nil))
      (CommentManager.get.apply_of_get? hManager hrefHasType hcGet))
    (.varRef (by yields_lookup))

/-- `comparisonFunction`'s body, evaluated at two refs the manager covers: two calls to
`expectComment`, built by `apply_expectComment`, two `structGet`s reading their timestamps, and
`Eval.Yields.le` over the two `Int`s — whose answer is `refLe manager a b`, by `refLe_eq_decide`,
which is the fact the caller (the sort's comparison premise) actually wants.

Nothing is asked of the two comments beyond the timestamps they carry: the reads are
`Value.field?` of whatever the calls returned, so the canonical form of a `Comment` value — which
this used to take apart to get at a `FieldValues` to look the field up in — costs nothing here. -/
private theorem CommentThread.linearize.apply_comparisonFunction_body {td : TypeDecls}
    {gs : Globals} {threads manager thread : Value} {a b ca cb : Value} {i j : Int} {env1 : Env}
    (hGet : gs.lookup "CommentManager.get" = some CommentManager.get)
    (hManager : manager.HasType td (.struct "CommentManager"))
    (ha : a.HasType td (.struct "CommentRef")) (hb : b.HasType td (.struct "CommentRef"))
    (hcaGet : CommentManager.get? manager a = some ca)
    (hcbGet : CommentManager.get? manager b = some cb)
    (hcai : ca.field? "createdTimestamp" = some (.int i))
    (hcbj : cb.field? "createdTimestamp" = some (.int j))
    (hexpect : env1.lookup "expectComment" =
      some ((CommentThread.linearize.callEnv gs [threads, manager, thread]).closure
        [("ref", Ty.struct "CommentRef")]
        (.optionMatch (.app (.varRef "CommentManager.get") [.varRef "manager", .varRef "ref"])
          (.unreachable (.struct "Comment") "Comments are required to be present in the manager")
          "c" (.varRef "c")))) :
    Eval td (Env.extend env1 [("a", Ty.struct "CommentRef"), ("b", Ty.struct "CommentRef")] [a, b])
      (.le (.structGet (.app (.varRef "expectComment") [.varRef "a"]) "createdTimestamp")
        (.structGet (.app (.varRef "expectComment") [.varRef "b"]) "createdTimestamp"))
      (.bool (decide (i ≤ j))) := by
  have hshift : (Env.extend env1 [("a", Ty.struct "CommentRef"), ("b", Ty.struct "CommentRef")]
      [a, b]).lookup "expectComment" = env1.lookup "expectComment" := by yields_lookup
  exact Eval.Yields.le
    (.structGet (CommentThread.linearize.apply_expectComment (threads := threads)
      (thread := thread) hGet hManager ha hcaGet (hshift.trans hexpect)
      (.varRef (by yields_lookup))) hcai)
    (.structGet (CommentThread.linearize.apply_expectComment (threads := threads)
      (thread := thread) hGet hManager hb hcbGet (hshift.trans hexpect)
      (.varRef (by yields_lookup))) hcbj)
    (by simp)

/-- A node the pool holds is held in its `commentTreeNodes` map under the ref it is registered
under, as the two premises `Eval.EHashmapGet` asks for: the map it ran in, and the answer
`KeyValues.lookup?` gave.

`CommentThreads.node?` is one `Value.lookupField?`, which collapses a missing field, a key no answer
could be given about and a key the map does not bind into one `none`; this is that read taken back
apart.  Where `CommentThreads.hasType_node?` spends the same lookup on the node's *type*, this
spends it on the lookup itself — which is what a proof building a get needs and what no inversion
proof here has needed, every one of them being handed the `KeyValues` by the `Eval` it inverts. -/
private theorem CommentThreads.lookup?_of_node? {threads ref node : Value} {kvs : KeyValues}
    (hfield : threads.field? "commentTreeNodes" = some (.hashmap kvs))
    (h : CommentThreads.node? threads ref = some node) :
    KeyValues.lookup? kvs ref = some (some node) := by
  simp only [CommentThreads.node?, Value.lookupField?, hfield] at h
  simpa [Option.join_eq_some_iff] using h

/-- The body of the flat mapping `linearize` runs over its children, at a child ref the pool has a
node for: the node is read out of `commentTreeNodes` — which is where `childrenRegistered` is spent,
the `none` branch being an `unreachable` and so having no value at all — and what the body returns
is what the recursive call on that node returned.

Abstracted over the environment the way `apply_expectComment` is, so that the caller need not write
out the three `let`s this sits under, and over `Env.Describes` rather than over one hypothesis per
name: the three names it reads, the one it resolves through the globals, and the globals themselves
are the whole of what it asks, which is one bundle and one `constructor` at the call site.

The bindings are asked for at `env.bindings` rather than at `Env.lookup` — which is `Env.Describes`'
own choice and the reason it has an `unshadowed` clause: the recursive call resolves *its own* name
through the globals, so saying that the three arguments are local bindings rather than globals of
those names is part of what makes the call the one `hLinearize` names. -/
private theorem CommentThread.linearize.eval_childBody {td : TypeDecls} {gs : Globals}
    {manager node r : Value} {cs : List Value} {env : Env} {thfvs : FieldValues} {kvs : KeyValues}
    (hLinearize : gs.lookup "CommentThread.linearize" = some CommentThread.linearize)
    (hEnv : Env.Describes env gs
      [("threads", .struct "CommentThreads" thfvs), ("manager", manager), ("childRef", r)]
      ["CommentThread.linearize"])
    (hnodes : thfvs.lookup "commentTreeNodes" = some (.hashmap kvs))
    (hlookup : KeyValues.lookup? kvs r = some (some node))
    (happly : CommentThread.linearize.Apply td gs
      [.struct "CommentThreads" thfvs, manager, node] (.list cs)) :
    Eval.Yields td env
      (.optionMatch
        (.hashmapGet (.structGet (.varRef "threads") "commentTreeNodes") (.varRef "childRef"))
        (.unreachable (.list (.struct "Comment"))
          "All comments must have an entry in commentTreeNodes")
        "childThread"
        (.app (.varRef "CommentThread.linearize")
          [.varRef "threads", .varRef "manager", .varRef "childThread"]))
      (.list cs) := by
  have hthreads := hEnv.lookup (x := "threads") (v := .struct "CommentThreads" thfvs) (by simp)
  have hmanager := hEnv.lookup (x := "manager") (v := manager) (by simp)
  have hchildRef := hEnv.lookup (x := "childRef") (v := r) (by simp)
  refine Eval.Yields.optionMatch_some
    (.hashmapGet (.structGet (.varRef hthreads) hnodes) (.varRef hchildRef) hlookup) ?_
  exact .app_global (by simpa [hEnv.globals] using hLinearize) (hEnv.unshadowed _ (by simp))
    (.cons (.varRef (by yields_lookup [hthreads])) (.cons (.varRef (by yields_lookup [hmanager]))
      (.cons (.varRef (by yields_lookup)) .nil)))
    (by simpa [hEnv.globals] using happly)

/-- A call to `linearize` on a node the pool holds has a value.
`Model.Declares`' docstring anticipates this one by name: it is what the fuel parameter the shallow
model carried used to buy, and the hypotheses are the invariants that bought it instead.

`childEdgeWf` is the recursion's measure, so being *registered* is what has to carry through the
induction — `CommentThreads.ChildEdge` relates a node to the node of one of its children and
requires the parent registered, which is why the induction hypothesis is stated of a node the pool
holds rather than of any node at all.  `childrenRegistered` is what keeps it carrying: a child ref
of a registered node is registered, so the `unreachable` on the `none` branch of
`threads.commentTreeNodes[childRef]` is never the branch taken.

The other two hypotheses pay for the other `unreachable` and for the sort.  `NodesCovered` says a
registered node names a comment the manager holds, which is what `expectComment` needs at the head
of the list and at each pair the sort compares; `CommentManager.WellFormed` is what gives those
comments `int` timestamps (`CommentManager.timestampIsInt`), which is what `refLe` compares and so
what makes `Eval.EListSortBy` have a `cmp` to be held to at every pair of children. -/
theorem CommentThread.linearize.apply_exists {td : TypeDecls} {gs : Globals}
    {threads manager thread ref : Value}
    (hDeclares : Model.Declares td gs)
    (hThreadsWF : CommentThreads.WellFormed td threads)
    (hManagerWF : CommentManager.WellFormed td manager)
    (hCovered : CommentThreads.NodesCovered manager threads)
    (hNode : CommentThreads.node? threads ref = some thread) :
    ∃ cs, CommentThread.linearize.Apply td gs [threads, manager, thread] (.list cs) := by
  -- The pool and the map its nodes are read out of, as *values*: this body reads them rather than
  -- being handed them by an `Eval` to invert.
  obtain ⟨thfvs, rfl⟩ := Value.eq_struct_of_hasType hThreadsWF.hasType
  obtain ⟨mv, hmfield, hmty⟩ :=
    Value.hasType_field hThreadsWF.hasType hDeclares.commentThreads
      (f := "commentTreeNodes") (t := .hashmap (.struct "CommentRef") (.struct "CommentThread")) rfl
  obtain ⟨kvs, rfl⟩ := Value.eq_hashmap_of_hasType hmty
  have hnodes : thfvs.lookup "commentTreeNodes" = some (.hashmap kvs) := by
    simpa [Value.field?] using hmfield
  refine WellFounded.induction hThreadsWF.childEdgeWf
    (C := fun t => (∃ r, CommentThreads.node? (.struct "CommentThreads" thfvs) r = some t) →
      ∃ cs, CommentThread.linearize.Apply td gs
        [.struct "CommentThreads" thfvs, manager, t] (.list cs))
    thread (fun t ih hreg => ?_) ⟨ref, hNode⟩
  obtain ⟨tref, htref⟩ := hreg
  have ht : t.HasType td (.struct "CommentThread") :=
    CommentThreads.hasType_node? hDeclares.toDeclaresTypes hThreadsWF htref
  obtain ⟨tfvs, rfl⟩ := Value.eq_struct_of_hasType ht
  -- The node names the ref it is registered under, and the manager has a comment for that ref.
  have hrootField : (Value.struct "CommentThread" tfvs).field? "value" = some tref :=
    hThreadsWF.rootMatchesKey _ _ htref
  have hrootTy : tref.HasType td (.struct "CommentRef") := by
    obtain ⟨rootv, hrootField', hrootTy⟩ :=
      Value.hasType_field ht hDeclares.commentThread (f := "value") (t := .struct "CommentRef") rfl
    obtain rfl : rootv = tref := Option.some.inj (hrootField'.symm.trans hrootField)
    exact hrootTy
  obtain ⟨rootComment, hrootGet⟩ := hCovered tref _ htref
  -- The children, every one of them registered and so every one of them covered.
  obtain ⟨chv, hchField, hchTy⟩ :=
    Value.hasType_field ht hDeclares.commentThread (f := "children")
      (t := .list (.struct "CommentRef")) rfl
  obtain ⟨childRefs, rfl, hchildTy⟩ := Value.eq_list_of_hasType hchTy
  have hchildNode : ∀ r ∈ childRefs, ∃ node,
      CommentThreads.node? (.struct "CommentThreads" thfvs) r = some node := fun r hr =>
    hThreadsWF.childrenRegistered tref _ childRefs r htref hchField hr
  have hchildStamp : ∀ r ∈ childRefs, ∃ c i, CommentManager.get? manager r = some c ∧
      c.field? "createdTimestamp" = some (.int i) := by
    intro r hr
    obtain ⟨node, hnode⟩ := hchildNode r hr
    obtain ⟨c, hc⟩ := hCovered r node hnode
    obtain ⟨i, hi⟩ := CommentManager.timestampIsInt hDeclares.toDeclaresTypes hManagerWF hc
    exact ⟨c, i, hc, hi⟩
  -- One list per child, each the answer to the recursive call on that child's node.  Stated under
  -- every environment that binds what the body reads, so the list is in hand before the `let`s the
  -- body sits under are built and `exists_zip_of_forall_exists` can collect them.
  have hchild : ∀ r ∈ childRefs, ∃ cs, ∀ env : Env,
      Env.Describes env gs
        [("threads", .struct "CommentThreads" thfvs), ("manager", manager), ("childRef", r)]
        ["CommentThread.linearize"] →
      Eval.Yields td env
        (.optionMatch
          (.hashmapGet (.structGet (.varRef "threads") "commentTreeNodes") (.varRef "childRef"))
          (.unreachable (.list (.struct "Comment"))
            "All comments must have an entry in commentTreeNodes")
          "childThread"
          (.app (.varRef "CommentThread.linearize")
            [.varRef "threads", .varRef "manager", .varRef "childThread"]))
        (.list cs) := by
    intro r hr
    obtain ⟨node, hnode⟩ := hchildNode r hr
    obtain ⟨cs, hcs⟩ := ih node ⟨tref, childRefs, r, htref, hchField, hr, hnode⟩ ⟨r, hnode⟩
    exact ⟨cs, fun env hEnv =>
      CommentThread.linearize.eval_childBody hDeclares.linearize hEnv hnodes
        (CommentThreads.lookup?_of_node? hmfield hnode) hcs⟩
  obtain ⟨vss, hvlen, hvev⟩ :=
    exists_zip_of_forall_exists (l := Value.sortWith (refLe manager) childRefs)
      fun r hr => hchild r (Value.mem_sortWith.mp hr)
  refine ⟨rootComment :: vss.flatten,
    .EApply _ (.cons "threads" hThreadsWF.hasType
      (.cons "manager" hManagerWF.hasType (.cons "thread" ht .nil))) ?_⟩
  -- `expectComment`, `comparisonFunction`, and the children in the order the sort puts them.
  refine Eval.Yields.let_ .lam ?_
  refine .let_ .lam ?_
  refine .let_ (.listSortBy (cmp := refLe manager)
    (.structGet (.varRef (by yields_lookup)) hchField) (.varRef rfl) ?cmp) ?_
  case cmp =>
    intro a ha b hb
    obtain ⟨ca, i, hcaGet, hcai⟩ := hchildStamp a ha
    obtain ⟨cb, j, hcbGet, hcbj⟩ := hchildStamp b hb
    refine ⟨.cons "a" (hchildTy a ha) (.cons "b" (hchildTy b hb) .nil), ?_⟩
    rw [refLe_eq_decide hcaGet hcai hcbGet hcbj]
    exact CommentThread.linearize.apply_comparisonFunction_body
      (threads := .struct "CommentThreads" thfvs) (thread := .struct "CommentThread" tfvs)
      hDeclares.get hManagerWF.hasType (hchildTy a ha) (hchildTy b hb) hcaGet hcbGet hcai hcbj
      (by yields_lookup)
  -- The thread's own comment, and then one run per child.
  refine .lcons
    (CommentThread.linearize.apply_expectComment
      (threads := .struct "CommentThreads" thfvs) (thread := .struct "CommentThread" tfvs)
      hDeclares.get hManagerWF.hasType hrootTy hrootGet (by yields_lookup)
      (.structGet (.varRef (by yields_lookup)) hrootField)) ?_
  exact .listFlatMap (.varRef (by yields_lookup)) .lam hvlen fun p hp =>
    ⟨.cons "childRef" (hchildTy p.1 (Value.mem_sortWith.mp (List.of_mem_zip hp).1)) .nil,
      hvev p hp _ (by constructor <;> yields_lookup [CommentThread.linearize])⟩

theorem CommentThread.linearize_hasAllThreadComments {td : TypeDecls} {gs : Globals}
    {threads manager thread : Value} {comments : List Value}
    (hDeclares : Model.Declares td gs)
    (h : CommentThread.linearize.Apply td gs [threads, manager, thread] (.list comments)) :
    ∀ ref, CommentThread.HasRef threads thread ref →
      ∃ c, CommentManager.get? manager ref = some c ∧ c ∈ comments := by
  intro ref hhas
  induction hhas generalizing comments with
  | root hvalue => grind [CommentThread.linearize.apply_inv]
  | child hchildField hchildMem hchildNode hrest ih =>
    grind [CommentThread.linearize.apply_inv]

theorem CommentThread.linearize_hasAllThreadComments_modelProgram
    (threads manager thread : Value) (comments : List Value)
    (h : modelProgram.Apply "CommentThread.linearize" [threads, manager, thread] (.list comments)) :
    ∀ ref, CommentThread.HasRef threads thread ref →
      ∃ c, CommentManager.get? manager ref = some c ∧ c ∈ comments := by
  obtain ⟨d, hd, happly⟩ := h
  obtain rfl : CommentThread.linearize = d := by
    simpa using (show modelProgram.lookup "CommentThread.linearize" =
      some CommentThread.linearize from rfl).symm.trans hd
  exact CommentThread.linearize_hasAllThreadComments Model.declares_modelProgram happly

/-! ## Going wrong

`Stuck` read along a body, which is the other half of progress — and it is now a corollary of the
half above rather than a second proof of it.  `Eval.not_stuck` (Lang/Progress.lean) says that an
expression with a value is not stuck, so `CommentThread.linearize.apply_exists` already answers for
every form this body and the bodies it calls into reach: the induction on `childEdgeWf`, the
invariants it spends and the places it spends them are written once, above.

What stood here was that proof read a second time for failure — one lemma per declaration
(`CommentManager.get`, `expectComment`, `comparisonFunction`, the body of the flat mapping over the
children) refuting each rule of `Stuck` in turn, with an inversion principle at every field read and
every call to the closure, because a mismatch rule speaks of the value a subexpression produced
rather than of a derivation.  Determinism (`Eval.unique`) is what makes all of that unnecessary: the
value a `Stuck` derivation's premise produced *is* the one the construction produced. -/

/-- A call to `linearize` on a node the pool holds never goes wrong.

`CommentThread.linearize.apply_exists` through `Eval.not_stuck`: the call has a value, and an
expression with a value does not reach a form no rule of `Eval` can fire on.

So this asks for exactly what the construction proof asks for and nothing more — `Globals.WellTyped`
in particular is gone, where the mirrored refutation proof needed it to read the result type of the
two calls whose values its mismatch rules objected to. -/
theorem CommentThread.linearize.not_stuck_body {td : TypeDecls} {gs : Globals}
    {threads manager thread ref : Value}
    (hDeclares : Model.Declares td gs)
    (hThreadsWF : CommentThreads.WellFormed td threads)
    (hManagerWF : CommentManager.WellFormed td manager)
    (hCovered : CommentThreads.NodesCovered manager threads)
    (hNode : CommentThreads.node? threads ref = some thread) :
    ¬Stuck td (CommentThread.linearize.callEnv gs [threads, manager, thread])
      CommentThread.linearize.body := by
  obtain ⟨cs, happly⟩ :=
    CommentThread.linearize.apply_exists hDeclares hThreadsWF hManagerWF hCovered hNode
  cases happly with
  | EApply _ _ hbody => exact Eval.not_stuck hbody

end
