module

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
private theorem exists_first_of_mem {α : Type} {l : List α} (P : α → Prop) {x : α} (hx : x ∈ l)
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
private theorem exists_mem_zip_of_mem_left {α β : Type} {as : List α} {bs : List β}
    (hlen : as.length = bs.length) {a : α} (ha : a ∈ as) : ∃ b, (a, b) ∈ as.zip bs := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  have hi' : i < bs.length := by omega
  exact ⟨bs[i], List.mem_zip_of_getElem? (List.getElem?_eq_getElem hi)
    (List.getElem?_eq_getElem hi')⟩

private theorem exists_mem_zip_of_mem_right {α β : Type} {as : List α} {bs : List β}
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
private theorem exists_zip_of_forall_exists {α β : Type} {l : List α} {P : α → β → Prop}
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
  obtain ⟨w, rfl⟩ : ∃ w, fvs = [("id", w)] := by
    rcases fvs with _ | ⟨⟨f, w⟩, _ | _⟩ <;> simp_all [CommentRef]
  obtain ⟨s, rfl⟩ := Value.hasType_string_iff.mp (htys "id" .string w rfl rfl)
  exact ⟨s, rfl⟩

/-- So comparing two of them has an answer, and the answer is whether they are the same value.

All three uses are read off this one statement: the answer exists at all, which is what rules out
`Stuck.equalsIncomparable`; it is `true` at a ref compared with itself, which is what makes a search
find the selected ref; and it is `false` at a ref that is not it, which is what makes the search
pass over the refs before it. -/
private theorem CommentRef.beq?_eq_some {td : TypeDecls} {a b : Value}
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
  simp [Env.lookup, List.lookup] at hltsv
  subst hltsv
  obtain rfl : groups = Value.sortWith cmp lts := by simpa using hgroups
  -- The threads at each location are what the call to `sortThreadLists` returned.
  obtain ⟨lrc, lts', _cb, _cg, _ps, _body, hlrcv, hsortFn, hslen, hsev, hlts'⟩ :=
    Eval.listMap_inv htsl
  obtain rfl : lts = lts' := by simpa using hlts'
  have hlrcvv := Eval.varRef_inv hlrcv
  have hsortFnv := Eval.varRef_inv hsortFn
  simp [Env.lookup, Env.closure, List.lookup] at hlrcvv hsortFnv
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hsortFnv
  subst hlrcvv
  -- Each of those lists of root comments was read out of the manager.
  obtain ⟨entries, lrc', _cb, _cg, _ps, _body, hentries, hlookupFn, helen, hlev, hlrc'⟩ :=
    Eval.listMap_inv hlrc
  obtain rfl : lrc = lrc' := by simpa using hlrc'
  have hlookupFnv := Eval.varRef_inv hlookupFn
  simp [Env.lookup, Env.closure, List.lookup] at hlookupFnv
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
    simp [Env.extend, Env.lookup, List.lookup] at hcFnv
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hcFnv
    have hmanagerComments : CommentManager.ContainsComments manager cs := by
      intro c hc
      obtain ⟨ref, hpair⟩ := exists_mem_zip_of_mem_right hclen hc
      obtain ⟨w, hcall, hbound⟩ := Eval.optionMatch_unreachable_inv (hcev _ hpair)
      have hw := Eval.varRef_inv hbound
      simp [Env.lookup, List.lookup] at hw
      subst hw
      obtain ⟨vs, hvlen, hvev, happly⟩ :=
        FuncDecl.apply_of_eval_app
          (by
            simpa [CommentThreads.asAlist, FuncDecl.callEnv, Env.extend, Globals.env]
              using hDeclares.get)
          (by simp [CommentThreads.asAlist, FuncDecl.callEnv, Env.extend, Globals.env,
            List.lookup]) hcall
      obtain ⟨a, b, rfl⟩ : ∃ a b, vs = [a, b] := by
        rcases vs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp_all
      have hav := Eval.varRef_inv (hvev (Expression.varRef "manager", a) (by simp))
      have hbv := Eval.varRef_inv (hvev (Expression.varRef "commentRef", b) (by simp))
      simp [CommentThreads.asAlist, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
        List.lookup] at hav hbv
      subst hav
      exact ⟨b, CommentManager.get.eq_get? happly⟩
    -- and the pair this location contributes is that location beside them
    obtain ⟨tvs, htvs, htlen, htev⟩ := Eval.tupleNew_inv hentry
    obtain ⟨a, b, rfl⟩ : ∃ a b, tvs = [a, b] := by
      rcases tvs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp_all
    have hav := Eval.varRef_inv (htev (Expression.varRef "loc", a) (by simp))
    have hbv := Eval.varRef_inv (htev (Expression.varRef "rootCommentsAtLoc", b) (by simp))
    simp [Env.lookup, List.lookup] at hav hbv
    subst hav
    subst hbv
    exact ⟨locv, cs, htvs, hmanagerComments⟩
  -- Putting the two together: the group, the location it is at, and the comments it came from.
  intro group hgroup
  obtain ⟨entry, hpair⟩ :=
    exists_mem_zip_of_mem_right hslen (Value.mem_sortWith.mp hgroup)
  obtain ⟨locatedThreads, hlpair⟩ := exists_mem_zip_of_mem_right helen (List.of_mem_zip hpair).1
  obtain ⟨loc, roots, rfl, hroots⟩ := hcomments _ hlpair
  obtain ⟨vs, hvlen, hvev, happly⟩ :=
    FuncDecl.apply_of_eval_app
      (by simpa [CommentThreads.asAlist, FuncDecl.callEnv, Env.extend, Globals.env] using
        hDeclares.sortThreadLists)
      (by simp [CommentThreads.asAlist, FuncDecl.callEnv, Env.extend, Globals.env, List.lookup])
      (hsev _ hpair)
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, vs = [a, b, c] := by
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩ <;> simp_all
  have hav := Eval.varRef_inv (hvev (Expression.varRef "threads", a) (by simp))
  have hbv := Eval.varRef_inv (hvev (Expression.varRef "manager", b) (by simp))
  have hcv := Eval.varRef_inv (hvev (Expression.varRef "locatedThreads", c) (by simp))
  simp [CommentThreads.asAlist, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
    List.lookup] at hav hbv hcv
  subst hav
  subst hbv
  subst hcv
  exact ⟨loc, roots, hroots,
    by simpa [CommentThreads.asAlist, FuncDecl.callEnv, Env.extend, Globals.env] using happly⟩


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
  simp [CommentThreads.asAlist.sortThreadLists, FuncDecl.callEnv, Env.extend, Globals.env,
    Env.lookup, List.lookup] at htvs
  subst htvs
  obtain rfl : roots = vs := by simpa using hget
  -- Each key is the timestamp its comment records, so each key is an `int`.
  obtain ⟨rfl, rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ ∧ _ := by
    simpa [Env.closure, Value.closure.injEq] using Eval.lam_inv hfun
  have hkeyField : ∀ p ∈ roots.zip ks, p.1.field? "createdTimestamp" = some p.2 := by
    intro p hp
    obtain ⟨_n, _fvs, hc, hf⟩ := Eval.structGet_inv (hkeys p hp)
    have hlc := Eval.varRef_inv hc
    simp [Env.extend, Env.lookup] at hlc
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
  simp [CommentThreads.asAlist.sortThreadLists, FuncDecl.callEnv, Env.extend, Env.closure,
    Globals.env, Env.lookup, List.lookup] at hsrv hfnv
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
    simp [Env.extend, Env.lookup, List.lookup] at hlt hlc hlth
    subst hlt
    subst hlth
    exact ⟨ref, by rw [hlc]; simpa [Value.field?] using hcr,
      by simp [CommentThreads.node?, Value.lookupField?, Value.field?, hcn, hlookup]⟩
  -- What comes back is the location beside those threads.
  obtain ⟨rvs, rfl, hrlen, hrev⟩ := Eval.tupleNew_inv hbody
  obtain ⟨a, b, rfl⟩ : ∃ a b, rvs = [a, b] := by
    rcases rvs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp_all
  obtain ⟨_rtvs, hloc, hloci⟩ :=
    Eval.tupleGet_inv (hrev ((Expression.varRef "commentThreadRoots").tupleGet 0, a) (by simp))
  have hlocv := Eval.varRef_inv hloc
  have hthreadsv := Eval.varRef_inv (hrev (Expression.varRef "sortedThreads", b) (by simp))
  simp [CommentThreads.asAlist.sortThreadLists, FuncDecl.callEnv, Env.extend, Globals.env,
    Env.lookup, List.lookup] at hlocv hthreadsv
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
    simpa [Env.closure, Value.closure.injEq] using Eval.lam_inv hfn
  obtain rfl : ordered = tss.flatten := by simpa using hres
  -- The groups are what the call to `asAlist` returned.
  obtain ⟨vs, hvlen, hvev, happly⟩ :=
    FuncDecl.apply_of_eval_app
      (by simpa [CommentThreads.toThreadsOrdered, FuncDecl.callEnv, Env.extend, Globals.env] using
        hDeclares.asAlist)
      (by simp [CommentThreads.toThreadsOrdered, FuncDecl.callEnv, Env.extend, Globals.env,
        List.lookup]) hcall
  obtain ⟨a, b, rfl⟩ : ∃ a b, vs = [a, b] := by
    rcases vs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp_all
  have hav := Eval.varRef_inv (hvev (Expression.varRef "threads", a) (by simp))
  have hbv := Eval.varRef_inv (hvev (Expression.varRef "manager", b) (by simp))
  simp [CommentThreads.toThreadsOrdered, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
    List.lookup] at hav hbv
  subst hav
  subst hbv
  simp only [FuncDecl.callEnv, Globals.env, Env.globals_extend] at happly
  refine ⟨groups, happly, fun group hgroup => ?_⟩
  obtain ⟨loc, ts, stamps, rfl, hlen, hstamps, hsorted⟩ :=
    CommentThreads.asAlist.threadLocationsSortedByTimestamp hDeclares
      hThreadsWF hManagerWF happly group hgroup
  -- And the group's own threads are one of the lists being run together.
  obtain ⟨l, hpair⟩ := exists_mem_zip_of_mem_left hflen hgroup
  obtain ⟨tvs, hscrut, hidx⟩ := Eval.tupleGet_inv (hfev _ hpair)
  have htvs := Eval.varRef_inv hscrut
  simp [Env.extend, Env.lookup] at htvs
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
        simpa [Env.lookup, Env.closure, Value.closure.injEq, List.lookup] using
          Eval.varRef_inv hf
      obtain ⟨root, rfl⟩ : ∃ root, argVals = [root] := by
        rcases argVals with _ | ⟨a, _ | _⟩ <;> simp_all
      obtain ⟨_tn, _tfvs, hthreadRef, hvalue⟩ :=
        Eval.structGet_inv
          (hargs ((Expression.varRef "thread").structGet "value", root) (by simp))
      have hthreadEq := Eval.varRef_inv hthreadRef
      simp [CommentThread.linearize, FuncDecl.callEnv, Env.extend, Globals.env,
        Env.lookup, List.lookup] at hthreadEq
      have hrootField : thread.field? "value" = some root := by
        rw [hthreadEq]; simpa [Value.field?] using hvalue
      -- The comment that ref names is the one the manager has under it.
      obtain ⟨c, hcall, hbound⟩ := Eval.optionMatch_unreachable_inv hcbody
      have hcv := Eval.varRef_inv hbound
      simp [Env.lookup, List.lookup] at hcv
      subst hcv
      obtain ⟨vs, hvlen, hvev, hgetApply⟩ :=
        FuncDecl.apply_of_eval_app
          (by simpa [CommentThread.linearize, FuncDecl.callEnv, Env.extend,
            Globals.env] using hDeclares.get)
          (by simp [CommentThread.linearize, FuncDecl.callEnv, Env.extend,
            Globals.env, List.lookup]) hcall
      obtain ⟨m, r, rfl⟩ : ∃ m r, vs = [m, r] := by
        rcases vs with _ | ⟨m, _ | ⟨r, _ | _⟩⟩ <;> simp_all
      have hmv := Eval.varRef_inv (hvev (Expression.varRef "manager", m) (by simp))
      have hrv := Eval.varRef_inv (hvev (Expression.varRef "ref", r) (by simp))
      simp [CommentThread.linearize, FuncDecl.callEnv, Env.extend, Globals.env,
        Env.lookup, List.lookup] at hmv hrv
      subst hmv
      subst hrv
      -- The rest of the list is one run per child, each the list that child's own call returned.
      obtain ⟨refs, lists, _fcb, _fcg, _fps, _fbody, hrefs, hfn, hflen, hfev, hlists⟩ :=
        Eval.listFlatMap_inv htail
      simp only [Value.list.injEq] at hlists
      subst hlists
      have hrefsv := Eval.varRef_inv hrefs
      simp [Env.lookup, List.lookup] at hrefsv
      obtain ⟨childRefs, cmp, hchildren, hsorted⟩ := Eval.listSortBy_inv hsort
      subst hrefsv
      obtain rfl : refs = Value.sortWith cmp childRefs := by simpa using hsorted
      obtain ⟨_cn, _cfvs, hthreadRef', hchildField⟩ := Eval.structGet_inv hchildren
      have hthreadEq' := Eval.varRef_inv hthreadRef'
      simp [CommentThread.linearize, FuncDecl.callEnv, Env.extend, Globals.env,
        Env.lookup, List.lookup] at hthreadEq'
      obtain ⟨rfl, rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ ∧ _ := by
        simpa [Env.closure, Value.closure.injEq] using Eval.lam_inv hfn
      refine ⟨root, c, childRefs, hrootField, CommentManager.get.eq_get? hgetApply, by simp,
        by rw [hthreadEq']; simpa [Value.field?] using hchildField, fun r hr => ?_⟩
      -- The child is one of the refs the flattening ran over, so one of the runs is its own.
      obtain ⟨cs, hpair⟩ := exists_mem_zip_of_mem_left hflen (Value.mem_sortWith.mpr hr)
      obtain ⟨node, hscrut, hreccall⟩ := Eval.optionMatch_unreachable_inv (hfev _ hpair)
      obtain ⟨kvs, vk, hm, hk, hlookup⟩ := Eval.hashmapGet_inv hscrut
      obtain ⟨_nn, _nfvs, hthreadsRef, hnodes⟩ := Eval.structGet_inv hm
      have hthreadsEq := Eval.varRef_inv hthreadsRef
      have hvk := Eval.varRef_inv hk
      simp [CommentThread.linearize, FuncDecl.callEnv, Env.extend, Globals.env,
        Env.lookup, List.lookup] at hthreadsEq hvk
      subst hvk
      have hnode : CommentThreads.node? threads r = some node := by
        rw [hthreadsEq]
        simp [CommentThreads.node?, Value.lookupField?, Value.field?, hnodes, hlookup]
      -- And that run is what the recursive call on the child's node returned.
      obtain ⟨rvs, hrvlen, hrvev, hrapply⟩ :=
        FuncDecl.apply_of_eval_app
          (by simpa [CommentThread.linearize, FuncDecl.callEnv, Env.extend,
            Globals.env] using hDeclares.linearize)
          (by simp [CommentThread.linearize, FuncDecl.callEnv, Env.extend,
            Globals.env, List.lookup]) hreccall
      obtain ⟨a, b, t', rfl⟩ : ∃ a b t', rvs = [a, b, t'] := by
        rcases rvs with _ | ⟨a, _ | ⟨b, _ | ⟨t', _ | _⟩⟩⟩ <;> simp_all
      have hav := Eval.varRef_inv (hrvev (Expression.varRef "threads", a) (by simp))
      have hbv := Eval.varRef_inv (hrvev (Expression.varRef "manager", b) (by simp))
      have htv := Eval.varRef_inv (hrvev (Expression.varRef "childThread", t') (by simp))
      simp [CommentThread.linearize, FuncDecl.callEnv, Env.extend, Globals.env,
        Env.lookup, List.lookup] at hav hbv htv
      subst hav
      subst hbv
      subst htv
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
    (hargE : Eval td callerEnv argE ref) :
    Eval td callerEnv (.app (.varRef "expectComment") [argE]) ca := by
  have hbody : Eval td
      (Env.extend (CommentThread.linearize.callEnv gs [threads, manager, thread])
        [("ref", Ty.struct "CommentRef")] [ref])
      (.optionMatch (.app (.varRef "CommentManager.get") [.varRef "manager", .varRef "ref"])
        (.unreachable (.struct "Comment") "Comments are required to be present in the manager")
        "c" (.varRef "c"))
      ca := by
    have hm : Eval td
        (Env.extend (CommentThread.linearize.callEnv gs [threads, manager, thread])
          [("ref", Ty.struct "CommentRef")] [ref]) (.varRef "manager") manager :=
      Eval.EVarRef _
        (by simp [CommentThread.linearize, FuncDecl.callEnv, Env.extend, Globals.env,
          Env.lookup, List.lookup])
    have hr : Eval td
        (Env.extend (CommentThread.linearize.callEnv gs [threads, manager, thread])
          [("ref", Ty.struct "CommentRef")] [ref]) (.varRef "ref") ref :=
      Eval.EVarRef _ (by simp [Env.extend, Env.lookup])
    have hscrut : Eval td
        (Env.extend (CommentThread.linearize.callEnv gs [threads, manager, thread])
          [("ref", Ty.struct "CommentRef")] [ref])
        (.app (.varRef "CommentManager.get") [.varRef "manager", .varRef "ref"])
        (.option (some ca)) :=
      FuncDecl.eval_app_of_apply hGet
        (by simp [CommentThread.linearize, FuncDecl.callEnv, Env.extend, Globals.env,
          List.lookup]) rfl
        (by
          intro p hp
          simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
            or_false] at hp
          rcases hp with rfl | rfl
          · exact hm
          · exact hr)
        (CommentManager.get.apply_of_get? hManager hrefHasType hcGet)
    exact Eval.EOptionMatchSome _ _ _ _ hscrut (Eval.EVarRef _ (by simp [Env.extend, Env.lookup]))
  exact Eval.EApp _ _ (Eval.EVarRef _ hcallerLookup) rfl
    (by
      intro p hp
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      obtain rfl := hp
      exact hargE)
    (.cons "ref" hrefHasType .nil) hbody

/-- `comparisonFunction`'s body, evaluated at two refs the manager covers: two calls to
`expectComment`, built by `apply_expectComment`, two `structGet`s reading their timestamps, and
`Eval.ELe` over the two `Int`s — whose answer is `refLe manager a b`, by `refLe_eq_decide`, which is
the fact the caller (`EListSortBy`'s comparability premise) actually wants. -/
private theorem CommentThread.linearize.apply_comparisonFunction_body {td : TypeDecls}
    {gs : Globals} {threads manager thread : Value} {a b ca cb : Value} {i j : Int} {env1 : Env}
    (hGet : gs.lookup "CommentManager.get" = some CommentManager.get)
    (hManager : manager.HasType td (.struct "CommentManager"))
    (ha : a.HasType td (.struct "CommentRef")) (hb : b.HasType td (.struct "CommentRef"))
    (hcaHasType : ca.HasType td (.struct "Comment")) (hcbHasType : cb.HasType td (.struct "Comment"))
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
  obtain ⟨fvsA, rfl⟩ := Value.eq_struct_of_hasType hcaHasType
  obtain ⟨fvsB, rfl⟩ := Value.eq_struct_of_hasType hcbHasType
  have hshift : (Env.extend env1 [("a", Ty.struct "CommentRef"), ("b", Ty.struct "CommentRef")]
      [a, b]).lookup "expectComment" = env1.lookup "expectComment" := by
    simp [Env.extend, Env.lookup, List.lookup]
  have hcallA : Eval td
      (Env.extend env1 [("a", Ty.struct "CommentRef"), ("b", Ty.struct "CommentRef")] [a, b])
      (.app (.varRef "expectComment") [.varRef "a"]) (.struct "Comment" fvsA) :=
    CommentThread.linearize.apply_expectComment (threads := threads) (thread := thread) hGet
      hManager ha hcaGet (hshift.trans hexpect) (Eval.EVarRef _ (by simp [Env.extend, Env.lookup]))
  have hcallB : Eval td
      (Env.extend env1 [("a", Ty.struct "CommentRef"), ("b", Ty.struct "CommentRef")] [a, b])
      (.app (.varRef "expectComment") [.varRef "b"]) (.struct "Comment" fvsB) :=
    CommentThread.linearize.apply_expectComment (threads := threads) (thread := thread) hGet
      hManager hb hcbGet (hshift.trans hexpect)
      (Eval.EVarRef _ (by simp [Env.extend, Env.lookup, List.lookup]))
  exact Eval.ELe _ _ (Eval.EStructGet _ _ hcallA hcai) (Eval.EStructGet _ _ hcallB hcbj) (by simp)

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

Abstracted over the environment the way `apply_expectComment` is, with one hypothesis per name the
body reads, so that the caller need not write out the three `let`s this sits under.  The bindings
are asked for at `env.bindings` rather than at `Env.lookup`: the recursive call resolves *its own*
name through the globals, so saying that the three arguments are local bindings rather than globals
of those names is part of what makes the call the one `hLinearize` names. -/
private theorem CommentThread.linearize.eval_childBody {td : TypeDecls} {gs : Globals}
    {manager node r : Value} {cs : List Value} {env : Env} {thfvs : FieldValues} {kvs : KeyValues}
    (hLinearize : gs.lookup "CommentThread.linearize" = some CommentThread.linearize)
    (hglobals : env.globals = gs)
    (hshadow : env.bindings.lookup "CommentThread.linearize" = none)
    (hthreads : env.bindings.lookup "threads" = some (.struct "CommentThreads" thfvs))
    (hmanager : env.bindings.lookup "manager" = some manager)
    (hchildRef : env.bindings.lookup "childRef" = some r)
    (hnodes : thfvs.lookup "commentTreeNodes" = some (.hashmap kvs))
    (hlookup : KeyValues.lookup? kvs r = some (some node))
    (happly : CommentThread.linearize.Apply td gs
      [.struct "CommentThreads" thfvs, manager, node] (.list cs)) :
    Eval td env
      (.optionMatch
        (.hashmapGet (.structGet (.varRef "threads") "commentTreeNodes") (.varRef "childRef"))
        (.unreachable (.list (.struct "Comment"))
          "All comments must have an entry in commentTreeNodes")
        "childThread"
        (.app (.varRef "CommentThread.linearize")
          [.varRef "threads", .varRef "manager", .varRef "childThread"]))
      (.list cs) := by
  refine Eval.EOptionMatchSome _ _ _ _
    (Eval.EHashmapGet _ _
      (Eval.EStructGet _ _ (Eval.EVarRef _ (Env.lookup_of_bindings hthreads)) hnodes)
      (Eval.EVarRef _ (Env.lookup_of_bindings hchildRef)) hlookup) ?_
  refine FuncDecl.eval_app_of_apply (x := "CommentThread.linearize")
    (by simpa [hglobals] using hLinearize) (by simp [List.lookup, hshadow]) rfl ?_
    (by simpa [hglobals] using happly)
  intro p hp
  simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact Eval.EVarRef _ (Env.lookup_of_bindings (by simp [List.lookup, hthreads]))
  · exact Eval.EVarRef _ (Env.lookup_of_bindings (by simp [List.lookup, hmanager]))
  · exact Eval.EVarRef _ (Env.lookup_of_bindings (by simp [List.lookup]))

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
  have hvalue : tfvs.lookup "value" = some tref := by simpa [Value.field?] using hrootField
  -- The children, every one of them registered and so every one of them covered.
  obtain ⟨chv, hchField, hchTy⟩ :=
    Value.hasType_field ht hDeclares.commentThread (f := "children")
      (t := .list (.struct "CommentRef")) rfl
  obtain ⟨childRefs, rfl, hchildTy⟩ := Value.eq_list_of_hasType hchTy
  have hchildren : tfvs.lookup "children" = some (.list childRefs) := by
    simpa [Value.field?] using hchField
  have hchildNode : ∀ r ∈ childRefs, ∃ node,
      CommentThreads.node? (.struct "CommentThreads" thfvs) r = some node := fun r hr =>
    hThreadsWF.childrenRegistered tref _ childRefs r htref hchField hr
  have hchildStamp : ∀ r ∈ childRefs, ∃ c i, CommentManager.get? manager r = some c ∧
      c.HasType td (.struct "Comment") ∧ c.field? "createdTimestamp" = some (.int i) := by
    intro r hr
    obtain ⟨node, hnode⟩ := hchildNode r hr
    obtain ⟨c, hc⟩ := hCovered r node hnode
    obtain ⟨i, hi⟩ := CommentManager.timestampIsInt hDeclares.toDeclaresTypes hManagerWF hc
    exact ⟨c, i, hc, CommentManager.hasType_get? hDeclares.toDeclaresTypes hManagerWF hc, hi⟩
  -- One list per child, each the answer to the recursive call on that child's node.  Stated under
  -- every environment that binds what the body reads, so the list is in hand before the `let`s the
  -- body sits under are built and `exists_zip_of_forall_exists` can collect them.
  have hchild : ∀ r ∈ childRefs, ∃ cs, ∀ env : Env, env.globals = gs →
      env.bindings.lookup "CommentThread.linearize" = none →
      env.bindings.lookup "threads" = some (.struct "CommentThreads" thfvs) →
      env.bindings.lookup "manager" = some manager →
      env.bindings.lookup "childRef" = some r →
      Eval td env
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
    exact ⟨cs, fun env hg hs hthreads hmanager hchildRef =>
      CommentThread.linearize.eval_childBody hDeclares.linearize hg hs hthreads hmanager hchildRef
        hnodes (CommentThreads.lookup?_of_node? hmfield hnode) hcs⟩
  obtain ⟨vss, hvlen, hvev⟩ :=
    exists_zip_of_forall_exists (l := Value.sortWith (refLe manager) childRefs)
      fun r hr => hchild r (Value.mem_sortWith.mp hr)
  refine ⟨rootComment :: vss.flatten,
    .EApply _ (.cons "threads" hThreadsWF.hasType
      (.cons "manager" hManagerWF.hasType (.cons "thread" ht .nil))) ?_⟩
  refine Eval.ELet _ _ _ (Eval.ELam _ _)
    (Eval.ELet _ _ _ (Eval.ELam _ _)
      (Eval.ELet (v₁ := .list (Value.sortWith (refLe manager) childRefs)) _ _ _ ?sort ?rest))
  case sort =>
    refine Eval.EListSortBy (cmp := refLe manager) _ _
      (Eval.EStructGet (name := "CommentThread") _ _
        (Eval.EVarRef _ (by
          simp [CommentThread.linearize, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
            List.lookup]))
        hchildren)
      (Eval.EVarRef _ rfl)
      (fun a ha b hb => .cons "a" (hchildTy a ha) (.cons "b" (hchildTy b hb) .nil)) ?_
    intro a ha b hb
    obtain ⟨ca, i, hcaGet, hcaTy, hcai⟩ := hchildStamp a ha
    obtain ⟨cb, j, hcbGet, hcbTy, hcbj⟩ := hchildStamp b hb
    rw [refLe_eq_decide hcaGet hcai hcbGet hcbj]
    exact CommentThread.linearize.apply_comparisonFunction_body
      (threads := .struct "CommentThreads" thfvs) (thread := .struct "CommentThread" tfvs)
      hDeclares.get hManagerWF.hasType
      (hchildTy a ha) (hchildTy b hb) hcaTy hcbTy hcaGet hcbGet hcai hcbj
      (by simp [Env.lookup, List.lookup])
  case rest =>
    refine Eval.ECons _ _
      (CommentThread.linearize.apply_expectComment
        (threads := .struct "CommentThreads" thfvs) (thread := .struct "CommentThread" tfvs)
        hDeclares.get hManagerWF.hasType hrootTy
        hrootGet (by simp [Env.lookup, List.lookup])
        (Eval.EStructGet (name := "CommentThread") _ _
          (Eval.EVarRef _ (by
            simp [CommentThread.linearize, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
              List.lookup]))
          hvalue))
      ?_
    refine Eval.EListFlatMap _ _ (Eval.EVarRef _ (by simp [Env.lookup, List.lookup]))
      (Eval.ELam _ _) hvlen
      (fun p hp => .cons "childRef"
        (hchildTy p.1 (Value.mem_sortWith.mp (List.of_mem_zip hp).1)) .nil) ?_
    intro p hp
    exact hvev p hp _
      (by simp [Env.extend, CommentThread.linearize, FuncDecl.callEnv, Globals.env])
      (by simp [Env.extend, CommentThread.linearize, FuncDecl.callEnv, Globals.env, List.lookup])
      (by simp [Env.extend, CommentThread.linearize, FuncDecl.callEnv, Globals.env, List.lookup])
      (by simp [Env.extend, CommentThread.linearize, FuncDecl.callEnv, Globals.env, List.lookup])
      (by simp [Env.extend])

theorem CommentThread.linearize_hasAllThreadComments {td : TypeDecls} {gs : Globals}
    {threads manager thread : Value} {comments : List Value}
    (hDeclares : Model.Declares td gs)
    (h : CommentThread.linearize.Apply td gs [threads, manager, thread] (.list comments)) :
    ∀ ref, CommentThread.HasRef threads thread ref →
      ∃ c, CommentManager.get? manager ref = some c ∧ c ∈ comments := by
  intro ref hhas
  induction hhas generalizing comments with
  | root hvalue =>
    obtain ⟨root, c, -, hroot, hget, hmem, -, -⟩ :=
      CommentThread.linearize.apply_inv hDeclares h
    obtain rfl := Option.some.inj (hroot.symm.trans hvalue)
    exact ⟨c, hget, hmem⟩
  | child hchildField hchildMem hchildNode hrest ih =>
    obtain ⟨root, c, childRefs, hroot, hget, hmem, hchildren, hkids⟩ :=
      CommentThread.linearize.apply_inv hDeclares h
    obtain rfl : childRefs = _ := by simpa [hchildren] using hchildField
    obtain ⟨node, cs, hnode, happly, hsub⟩ := hkids _ hchildMem
    obtain rfl : node = _ := Option.some.inj (hnode.symm.trans hchildNode)
    obtain ⟨c', hget', hmem'⟩ := ih happly
    exact ⟨c', hget', hsub c' hmem'⟩

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

/-! ## Going wrong, declaration by declaration

`Stuck` read along a body, which is the other half of progress.  It is not a statement about one
body: `Stuck.appBody` says a call is stuck wherever the body it enters is, so the declarations this
one calls have to be walked to the bottom — `CommentThread.linearize` and, through it,
`CommentManager.get`.

Every mismatch rule of `Stuck` carries `Eval` premises about the subexpressions, so refuting one is
*reading* the value a subexpression produced.  That is why each lemma below comes with whatever
inversion its own mismatch rules need, and it is why `Eval` being deterministic is never wanted: the
value a `Stuck` derivation's premise produced need not be the one a separate `Eval` derivation
produced, so what rules the mismatch out has to be read off that premise.

What a form of the language goes wrong in is the language's business, so the refutation rules form
by form — `Stuck.not_let`, `Stuck.not_app_varRef` and their neighbours, one per form these bodies
use — live beside `Stuck` itself in `Lang/Progress.lean`, together with the inversion
(`Eval.structGet_varRef_eq`) their mismatch rules are read with.  What is left here is what those
lemmas have to be handed: the invariants, declaration by declaration. -/

/-! ### `CommentManager.get`

The bottom of the chain: one `hashmapGet` over one field.  The two things that can go wrong are the
field not being a hashmap and the key having no answer in it, and `CommentManager.get? manager ref =
some c` rules out both at once — it *is* the lookup having an answer, which is what
`CommentManager.eq_hashmap_of_get?` takes it apart into. -/

/-- A comment the manager holds under `ref` is held in its `comments` map, as the two premises
`Eval.EHashmapGet` asks for.  `CommentThreads.lookup?_of_node?` for the manager, with the field read
existential rather than given: a caller of this has the invariant and not the map. -/
private theorem CommentManager.eq_hashmap_of_get? {manager ref c : Value}
    (h : CommentManager.get? manager ref = some c) :
    ∃ kvs, manager.field? "comments" = some (.hashmap kvs) ∧
      KeyValues.lookup? kvs ref = some (some c) := by
  rw [CommentManager.get?, Value.lookupField?] at h
  split at h
  · next kvs heq => exact ⟨kvs, heq, by simpa [Option.join_eq_some_iff] using h⟩
  · simp at h

private theorem CommentManager.get.not_stuck_body {td : TypeDecls} {gs : Globals}
    {manager ref c : Value} (hget : CommentManager.get? manager ref = some c) :
    ¬Stuck td (CommentManager.get.callEnv gs [manager, ref]) CommentManager.get.body := by
  obtain ⟨kvs, hfield, hlookup⟩ := CommentManager.eq_hashmap_of_get? hget
  have hm : (CommentManager.get.callEnv gs [manager, ref]).lookup "manager" = some manager := by
    simp [CommentManager.get, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup]
  have hk : (CommentManager.get.callEnv gs [manager, ref]).lookup "ref" = some ref := by
    simp [CommentManager.get, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup, List.lookup]
  rintro hs
  cases hs with
  | hashmapGetMap h => exact Stuck.not_structGet_varRef hm hfield h
  | hashmapGetMapNotHashmap hev hnh =>
    obtain rfl := Eval.structGet_varRef_eq hm hfield hev
    exact hnh ⟨_, rfl⟩
  | hashmapGetKey h => exact Stuck.not_varRef hk h
  | hashmapGetIncomparable hev hkev hnone =>
    have heq := Eval.structGet_varRef_eq hm hfield hev
    simp only [Value.hashmap.injEq] at heq
    subst heq
    obtain rfl := Option.some.inj ((Eval.varRef_inv hkev).symm.trans hk)
    simp [hlookup] at hnone

/-! ### `CommentThread.linearize`

One level up, and where the recursion is paid for a second time: `Stuck.appBody` says the call on a
child is stuck wherever that child's own body is, so this is the same well-founded induction on
`childEdgeWf` that `CommentThread.linearize.apply_exists` is, read for failure rather than for a
value.  The invariants are spent in the same places — `NodesCovered` at `expectComment`,
`childrenRegistered` at the lookup in `commentTreeNodes`, `CommentManager.WellFormed` at the
timestamps the sort compares — and `childEdgeWf` is again what makes the descent terminate.

The closure `linearize` lets over its manager is dealt with first, as it is there: it is called from
the head of the list and from each pair the sort compares, so what it does is a fact about the
closure rather than about either call site.  Two facts, where the construction proof needed one — it
is not stuck, and what it produced was the comment — because a mismatch rule outside such a call
speaks of the value the call produced. -/

/-- What a call to `expectComment` produced: the comment the manager holds under the ref it was
handed, and nothing else.

`CommentThread.linearize.apply_expectComment` read backwards, and what the mismatch rules outside
such a call need — `Stuck.structGetMissing` and `Stuck.leIncomparable` both speak of the value a
subexpression produced, so refuting them is reading it.  Stated over every value the argument
expression can produce, and so over every value the call can, because nothing here makes `Eval`
deterministic.

The environment the closure captured is `cenv` rather than the call environment `linearize` lets it
over, with the three facts this reads of it — the globals it resolves names through, that nothing
local shadows `CommentManager.get`, and what `manager` is bound to — as hypotheses.  That is what
lets a caller name the environment it is already holding instead of writing the call out again, and
it is all the body of this closure reads. -/
private theorem CommentThread.linearize.eval_expectComment_eq {td : TypeDecls} {gs : Globals}
    {cenv callerEnv : Env} {argE : Expression} {manager ref ca v : Value}
    (hGet : gs.lookup "CommentManager.get" = some CommentManager.get)
    (hGlobals : cenv.globals = gs)
    (hShadow : cenv.bindings.lookup "CommentManager.get" = none)
    (hManagerBinding : cenv.bindings.lookup "manager" = some manager)
    (hcGet : CommentManager.get? manager ref = some ca)
    (hcallerLookup : callerEnv.lookup "expectComment" =
      some (cenv.closure [("ref", Ty.struct "CommentRef")]
        (.optionMatch (.app (.varRef "CommentManager.get") [.varRef "manager", .varRef "ref"])
          (.unreachable (.struct "Comment") "Comments are required to be present in the manager")
          "c" (.varRef "c"))))
    (hargE : ∀ u, Eval td callerEnv argE u → u = ref)
    (h : Eval td callerEnv (.app (.varRef "expectComment") [argE]) v) : v = ca := by
  cases h with
  | @EApp _env _cb _cg _ps _lbody argVals _v _ _ hf hlen hargs _ hcbody =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ ∧ _ := by
      simpa [Env.closure, Value.closure.injEq] using
        Option.some.inj ((Eval.varRef_inv hf).symm.trans hcallerLookup)
    obtain ⟨a, rfl⟩ : ∃ a, argVals = [a] := by
      rcases argVals with _ | ⟨a, _ | _⟩ <;> simp_all
    obtain rfl := hargE a (hargs (argE, a) (by simp))
    -- The comment the ref names is the one the manager has under it.
    obtain ⟨c, hcall, hbound⟩ := Eval.optionMatch_unreachable_inv hcbody
    have hcv := Eval.varRef_inv hbound
    simp [Env.lookup, List.lookup] at hcv
    subst hcv
    obtain ⟨vs, hvlen, hvev, hgetApply⟩ :=
      FuncDecl.apply_of_eval_app
        (by simpa [Env.extend, hGlobals] using hGet)
        (by simp [Env.extend, List.lookup, hShadow]) hcall
    obtain ⟨m, r, rfl⟩ : ∃ m r, vs = [m, r] := by
      rcases vs with _ | ⟨m, _ | ⟨r, _ | _⟩⟩ <;> simp_all
    have hmv := Eval.varRef_inv (hvev (Expression.varRef "manager", m) (by simp))
    have hrv := Eval.varRef_inv (hvev (Expression.varRef "ref", r) (by simp))
    simp [Env.extend, Env.lookup, List.lookup, hManagerBinding] at hmv hrv
    subst hmv
    subst hrv
    exact Option.some.inj
      ((CommentManager.get.eq_get? (by simpa [Env.extend, hGlobals] using hgetApply)).symm.trans
        hcGet)

/-- And that the call is not stuck: `expectComment`'s body, under the one binding a call to it makes,
at a ref the manager covers.

Three of the four rules of `Stuck` for a match on an option are refuted by the call to
`CommentManager.get` the scrutinee is — not stuck by `CommentManager.get.not_stuck_body`, and
producing an option because that is what the declaration's result type says — and the fourth,
`optionMatchNone`, by `Stuck.not_unreachable`: the branch a ref the manager does not cover would take
is the one form nothing is stuck at. -/
private theorem CommentThread.linearize.not_stuck_expectComment_body {td : TypeDecls}
    {gs : Globals} {cenv : Env} {manager ref ca : Value}
    (hWellTyped : Globals.WellTyped td gs)
    (hGet : gs.lookup "CommentManager.get" = some CommentManager.get)
    (hGlobals : cenv.globals = gs)
    (hShadow : cenv.bindings.lookup "CommentManager.get" = none)
    (hManagerBinding : cenv.bindings.lookup "manager" = some manager)
    (hManager : manager.HasType td (.struct "CommentManager"))
    (hrefHasType : ref.HasType td (.struct "CommentRef"))
    (hcGet : CommentManager.get? manager ref = some ca) :
    ¬Stuck td (Env.extend cenv [("ref", Ty.struct "CommentRef")] [ref])
      (.optionMatch (.app (.varRef "CommentManager.get") [.varRef "manager", .varRef "ref"])
        (.unreachable (.struct "Comment") "Comments are required to be present in the manager")
        "c" (.varRef "c")) := by
  have hm : (Env.extend cenv [("ref", Ty.struct "CommentRef")] [ref]).lookup "manager" =
      some manager := by
    simp [Env.extend, Env.lookup, List.lookup, hManagerBinding]
  have hr : (Env.extend cenv [("ref", Ty.struct "CommentRef")] [ref]).lookup "ref" = some ref := by
    simp [Env.extend, Env.lookup]
  -- The arguments the call passes are the manager and the ref, whatever derivation produced them.
  have hvs : ∀ vs : List Value, [Expression.varRef "manager", Expression.varRef "ref"].length =
      vs.length →
      (∀ p ∈ [Expression.varRef "manager", Expression.varRef "ref"].zip vs,
        Eval td (Env.extend cenv [("ref", Ty.struct "CommentRef")] [ref]) p.1 p.2) →
      vs = [manager, ref] := by
    intro vs hlen hev
    obtain ⟨m, r, rfl⟩ : ∃ m r, vs = [m, r] := by
      rcases vs with _ | ⟨m, _ | ⟨r, _ | _⟩⟩ <;> simp_all
    obtain rfl := Option.some.inj
      ((Eval.varRef_inv (hev (Expression.varRef "manager", m) (by simp))).symm.trans hm)
    obtain rfl := Option.some.inj
      ((Eval.varRef_inv (hev (Expression.varRef "ref", r) (by simp))).symm.trans hr)
    rfl
  refine Stuck.not_optionMatch_unreachable
    (Stuck.not_app_global (d := CommentManager.get) (by simpa [Env.extend, hGlobals] using hGet)
      (by simp [Env.extend, List.lookup, hShadow]) ?_ ?_ ?_) ?_ ?_
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact Stuck.not_varRef hm
    · rcases List.mem_cons.mp ha' with rfl | ha''
      · exact Stuck.not_varRef hr
      · simp at ha''
  · intro vs hlen hev
    obtain rfl := hvs vs hlen hev
    exact .cons "manager" hManager (.cons "ref" hrefHasType .nil)
  · intro vs hlen hev
    obtain rfl := hvs vs hlen hev
    simpa [Env.extend, hGlobals] using
      CommentManager.get.not_stuck_body (td := td) (gs := gs) hcGet
  · intro v hv
    obtain ⟨vs, hvlen, hvev, happly⟩ :=
      FuncDecl.apply_of_eval_app (by simpa [Env.extend, hGlobals] using hGet)
        (by simp [Env.extend, List.lookup, hShadow]) hv
    have happly' : CommentManager.get.Apply td gs vs v := by
      simpa [Env.extend, hGlobals] using happly
    exact Value.isOption_of_hasType (t := .struct "Comment")
      (happly'.hasType hWellTyped (hWellTyped _ _ hGet))
  · intro w hw
    exact Stuck.not_varRef (v := w) (by simp [Env.lookup, List.lookup])

/-- `comparisonFunction`'s body is not stuck at two refs the manager covers: two calls to
`expectComment`, two field reads off what they produced, and `Value.le?` on the two `Int`s those
reads found — which is the one thing `Stuck.leIncomparable` has to be refuted by, and where the
comments' timestamps being `int`s is spent.

`CommentThread.linearize.apply_comparisonFunction_body`'s counterpart, and abstracted over the
environment the same way, except that the two names are asked for by `Env.lookup` rather than
supplied by an `Env.extend`: the caller has them from whatever `Stuck.listSortByCall` handed it. -/
private theorem CommentThread.linearize.not_stuck_comparisonFunction_body {td : TypeDecls}
    {gs : Globals} {cenv env : Env} {manager a b ca cb : Value} {i j : Int}
    (hWellTyped : Globals.WellTyped td gs)
    (hGet : gs.lookup "CommentManager.get" = some CommentManager.get)
    (hGlobals : cenv.globals = gs)
    (hShadow : cenv.bindings.lookup "CommentManager.get" = none)
    (hManagerBinding : cenv.bindings.lookup "manager" = some manager)
    (hManager : manager.HasType td (.struct "CommentManager"))
    (ha : a.HasType td (.struct "CommentRef")) (hb : b.HasType td (.struct "CommentRef"))
    (hcaGet : CommentManager.get? manager a = some ca)
    (hcbGet : CommentManager.get? manager b = some cb)
    (hcai : ca.field? "createdTimestamp" = some (.int i))
    (hcbj : cb.field? "createdTimestamp" = some (.int j))
    (haLookup : env.lookup "a" = some a) (hbLookup : env.lookup "b" = some b)
    (hexpect : env.lookup "expectComment" =
      some (cenv.closure [("ref", Ty.struct "CommentRef")]
        (.optionMatch (.app (.varRef "CommentManager.get") [.varRef "manager", .varRef "ref"])
          (.unreachable (.struct "Comment") "Comments are required to be present in the manager")
          "c" (.varRef "c")))) :
    ¬Stuck td env
      (.le (.structGet (.app (.varRef "expectComment") [.varRef "a"]) "createdTimestamp")
        (.structGet (.app (.varRef "expectComment") [.varRef "b"]) "createdTimestamp")) := by
  -- One side of the comparison, read at either of the two names.
  have hside : ∀ (x : String) (r cr : Value) (k : Int), env.lookup x = some r →
      r.HasType td (.struct "CommentRef") → CommentManager.get? manager r = some cr →
      cr.field? "createdTimestamp" = some (.int k) →
      ¬Stuck td env (.structGet (.app (.varRef "expectComment") [.varRef x]) "createdTimestamp") ∧
        ∀ u, Eval td env
          (.structGet (.app (.varRef "expectComment") [.varRef x]) "createdTimestamp") u →
          u = .int k := by
    intro x r cr k hx hrty hrGet hk
    have hargE : ∀ u, Eval td env (.varRef x) u → u = r :=
      fun u hu => Option.some.inj ((Eval.varRef_inv hu).symm.trans hx)
    have hcallEq : ∀ u, Eval td env (.app (.varRef "expectComment") [.varRef x]) u → u = cr :=
      fun u hu => CommentThread.linearize.eval_expectComment_eq hGet hGlobals hShadow
        hManagerBinding hrGet hexpect hargE hu
    refine ⟨Stuck.not_structGet (Stuck.not_app_varRef hexpect ?_ ?_ ?_)
        (fun v hv => ⟨.int k, by rw [hcallEq v hv]; exact hk⟩),
      fun u hu => Eval.structGet_eq (fun v hv => by rw [hcallEq v hv]; exact hk) hu⟩
    · intro e he
      obtain rfl : e = Expression.varRef x := by simpa using he
      exact Stuck.not_varRef hx
    · intro vs hlen hev
      obtain ⟨v, rfl⟩ : ∃ v, vs = [v] := by
        rcases vs with _ | ⟨v, _ | _⟩ <;> simp_all
      obtain rfl := hargE v (hev (Expression.varRef x, v) (by simp))
      exact .cons "ref" hrty .nil
    · intro vs hlen hev
      obtain ⟨v, rfl⟩ : ∃ v, vs = [v] := by
        rcases vs with _ | ⟨v, _ | _⟩ <;> simp_all
      obtain rfl := hargE v (hev (Expression.varRef x, v) (by simp))
      exact CommentThread.linearize.not_stuck_expectComment_body hWellTyped hGet hGlobals hShadow
        hManagerBinding hManager hrty hrGet
  obtain ⟨hlStuck, hlEq⟩ := hside "a" a ca i haLookup ha hcaGet hcai
  obtain ⟨hrStuck, hrEq⟩ := hside "b" b cb j hbLookup hb hcbGet hcbj
  refine Stuck.not_le hlStuck hrStuck fun v₁ v₂ h₁ h₂ => ?_
  rw [hlEq v₁ h₁, hrEq v₂ h₂]
  simp

/-- Whatever the body of the flat mapping `linearize` runs over its children produced is a list,
which is what `Stuck.listFlatMapCallNotList` asks of a call.

The only fact about this body that needs the globals to check: the branch that has a value is the
recursive call, and what a call produces is of the declaration's result type, which for `linearize`
is a list. -/
private theorem CommentThread.linearize.isList_childBody {td : TypeDecls} {gs : Globals}
    {u : Value} {env : Env}
    (hWellTyped : Globals.WellTyped td gs)
    (hLinearize : gs.lookup "CommentThread.linearize" = some CommentThread.linearize)
    (hGlobals : env.globals = gs)
    (hShadow : env.bindings.lookup "CommentThread.linearize" = none)
    (h : Eval td env
      (.optionMatch
        (.hashmapGet (.structGet (.varRef "threads") "commentTreeNodes") (.varRef "childRef"))
        (.unreachable (.list (.struct "Comment")) "All comments must have an entry in commentTreeNodes") "childThread"
        (.app (.varRef "CommentThread.linearize")
          [.varRef "threads", .varRef "manager", .varRef "childThread"])) u) : u.IsList := by
  obtain ⟨w, -, hbody⟩ := Eval.optionMatch_unreachable_inv h
  obtain ⟨vs, hvlen, hvev, happly⟩ :=
    FuncDecl.apply_of_eval_app (by simpa [hGlobals] using hLinearize)
      (by simp [List.lookup, hShadow]) hbody
  have happly' : CommentThread.linearize.Apply td gs vs u := by simpa [hGlobals] using happly
  exact Value.isList_of_hasType (t := .struct "Comment")
    (happly'.hasType hWellTyped (hWellTyped _ _ hLinearize))

/-- And that body is not stuck at a child ref the pool has a node for.

`CommentThread.linearize.eval_childBody`'s counterpart, abstracted over the environment the same
way, and with the recursive call's own progress — `hrec` — as a hypothesis: that is where the
induction goes, exactly as the construction proof passes its induction hypothesis in here.

The `none` branch is the `unreachable` `childrenRegistered` pays for, and it is paid twice over:
`Stuck.not_unreachable` refutes `optionMatchNone` whatever the lookup answered, and `hnode` is what
makes `Stuck.hashmapGetIncomparable` impossible — the key has an answer, so the get is not stuck
either. -/
private theorem CommentThread.linearize.not_stuck_childBody {td : TypeDecls} {gs : Globals}
    {threads manager node r : Value} {kvs : KeyValues} {env : Env}
    (hLinearize : gs.lookup "CommentThread.linearize" = some CommentThread.linearize)
    (hGlobals : env.globals = gs)
    (hShadow : env.bindings.lookup "CommentThread.linearize" = none)
    (hthreadsBinding : env.bindings.lookup "threads" = some threads)
    (hmanagerBinding : env.bindings.lookup "manager" = some manager)
    (hchildRefBinding : env.bindings.lookup "childRef" = some r)
    (hnodesField : threads.field? "commentTreeNodes" = some (.hashmap kvs))
    (hthreadsTy : threads.HasType td (.struct "CommentThreads"))
    (hmanagerTy : manager.HasType td (.struct "CommentManager"))
    (hnodeTy : node.HasType td (.struct "CommentThread"))
    (hnode : CommentThreads.node? threads r = some node)
    (hrec : ¬Stuck td (CommentThread.linearize.callEnv gs [threads, manager, node])
      CommentThread.linearize.body) :
    ¬Stuck td env
      (.optionMatch
        (.hashmapGet (.structGet (.varRef "threads") "commentTreeNodes") (.varRef "childRef"))
        (.unreachable (.list (.struct "Comment"))
          "All comments must have an entry in commentTreeNodes")
        "childThread"
        (.app (.varRef "CommentThread.linearize")
          [.varRef "threads", .varRef "manager", .varRef "childThread"])) := by
  have hlookup : KeyValues.lookup? kvs r = some (some node) :=
    CommentThreads.lookup?_of_node? hnodesField hnode
  have hthreadsLookup : env.lookup "threads" = some threads := Env.lookup_of_bindings
    hthreadsBinding
  have hchildRefLookup : env.lookup "childRef" = some r := Env.lookup_of_bindings hchildRefBinding
  -- The node the get found is the registered one, whatever derivation found it.
  have hsome : ∀ u, Eval td env
      (.hashmapGet (.structGet (.varRef "threads") "commentTreeNodes") (.varRef "childRef"))
      (.option (some u)) → u = node := by
    intro u hu
    obtain ⟨kvs', vk, hm, hk, hl⟩ := Eval.hashmapGet_inv hu
    have heq := Eval.structGet_varRef_eq hthreadsLookup hnodesField hm
    simp only [Value.hashmap.injEq] at heq
    subst heq
    obtain rfl := Option.some.inj ((Eval.varRef_inv hk).symm.trans hchildRefLookup)
    exact Option.some.inj (Option.some.inj (hl.symm.trans hlookup))
  -- The arguments the recursive call passes are the pool, the manager and that node.
  have hargs : ∀ (u : Value) (vs : List Value),
      [Expression.varRef "threads", Expression.varRef "manager",
        Expression.varRef "childThread"].length = vs.length →
      (∀ p ∈ [Expression.varRef "threads", Expression.varRef "manager",
        Expression.varRef "childThread"].zip vs,
        Eval td ⟨("childThread", u) :: env.bindings, env.globals⟩ p.1 p.2) →
      vs = [threads, manager, u] := by
    intro u vs hlen hev
    obtain ⟨x, y, z, rfl⟩ : ∃ x y z, vs = [x, y, z] := by
      rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | _⟩⟩⟩ <;> simp_all
    have hxv := Eval.varRef_inv (hev (Expression.varRef "threads", x) (by simp))
    have hyv := Eval.varRef_inv (hev (Expression.varRef "manager", y) (by simp))
    have hzv := Eval.varRef_inv (hev (Expression.varRef "childThread", z) (by simp))
    simp [Env.lookup, List.lookup, hthreadsBinding, hmanagerBinding] at hxv hyv hzv
    simp [hxv, hyv, hzv]
  refine Stuck.not_optionMatch_unreachable ?_ (fun v hv => Eval.isOption_hashmapGet hv) ?_
  · refine Stuck.not_hashmapGet (Stuck.not_structGet_varRef hthreadsLookup hnodesField)
      (Stuck.not_varRef hchildRefLookup) (fun v hv => ?_) (fun kvs' vk hm hk => ?_)
    · rw [Eval.structGet_varRef_eq hthreadsLookup hnodesField hv]
      exact ⟨_, rfl⟩
    · have heq := Eval.structGet_varRef_eq hthreadsLookup hnodesField hm
      simp only [Value.hashmap.injEq] at heq
      subst heq
      obtain rfl := Option.some.inj ((Eval.varRef_inv hk).symm.trans hchildRefLookup)
      simp [hlookup]
  · intro u hu
    obtain rfl := hsome u hu
    refine Stuck.not_app_global (d := CommentThread.linearize)
      (by simpa [hGlobals] using hLinearize) (by simp [List.lookup, hShadow]) ?_ ?_ ?_
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact Stuck.not_varRef (v := threads)
          (by simp [Env.lookup, List.lookup, hthreadsBinding])
      · rcases List.mem_cons.mp ha' with rfl | ha''
        · exact Stuck.not_varRef (v := manager)
            (by simp [Env.lookup, List.lookup, hmanagerBinding])
        · rcases List.mem_cons.mp ha'' with rfl | ha'''
          · exact Stuck.not_varRef (v := u) (by simp [Env.lookup, List.lookup])
          · simp at ha'''
    · intro vs hlen hev
      obtain rfl := hargs u vs hlen hev
      exact .cons "threads" hthreadsTy (.cons "manager" hmanagerTy (.cons "thread" hnodeTy .nil))
    · intro vs hlen hev
      obtain rfl := hargs u vs hlen hev
      simpa [hGlobals] using hrec

/-- A call to `linearize` on a node the pool holds never goes wrong.

`CommentThread.linearize.apply_exists` read for failure: the same induction on `childEdgeWf`, the
same invariants, spent in the same places.  What `Stuck` adds over the construction is that every
value a subexpression *could* have produced has to be answered for and not just the ones a
derivation was built from, so the inversions — `Eval.structGet_varRef_eq` at every field read,
`eval_expectComment_eq` at every call to the closure — are where this proof's work goes, where the
construction's went into the rules of `Eval`.

`hWellTyped` is the one hypothesis the construction proof did not need.  Two mismatch rules ask what
a *call* produced — `Stuck.optionMatchNotOption` of the get inside `expectComment`, and
`Stuck.listFlatMapCallNotList` of the recursive call — and the answer is the declaration's result
type, which is `FuncDecl.Apply.hasType` and so the globals checking. -/
theorem CommentThread.linearize.not_stuck_body {td : TypeDecls} {gs : Globals}
    {threads manager thread ref : Value}
    (hWellTyped : Globals.WellTyped td gs)
    (hDeclares : Model.Declares td gs)
    (hThreadsWF : CommentThreads.WellFormed td threads)
    (hManagerWF : CommentManager.WellFormed td manager)
    (hCovered : CommentThreads.NodesCovered manager threads)
    (hNode : CommentThreads.node? threads ref = some thread) :
    ¬Stuck td (CommentThread.linearize.callEnv gs [threads, manager, thread])
      CommentThread.linearize.body := by
  -- The pool and the map its nodes are read out of, as *values*, exactly as in `apply_exists`.
  obtain ⟨thfvs, rfl⟩ := Value.eq_struct_of_hasType hThreadsWF.hasType
  obtain ⟨mv, hmfield, hmty⟩ :=
    Value.hasType_field hThreadsWF.hasType hDeclares.commentThreads
      (f := "commentTreeNodes") (t := .hashmap (.struct "CommentRef") (.struct "CommentThread")) rfl
  obtain ⟨kvs, rfl⟩ := Value.eq_hashmap_of_hasType hmty
  refine WellFounded.induction hThreadsWF.childEdgeWf
    (C := fun t => (∃ r, CommentThreads.node? (.struct "CommentThreads" thfvs) r = some t) →
      ¬Stuck td (CommentThread.linearize.callEnv gs
        [.struct "CommentThreads" thfvs, manager, t]) CommentThread.linearize.body)
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
  have hchildStamp : ∀ r ∈ childRefs, ∃ c k, CommentManager.get? manager r = some c ∧
      c.field? "createdTimestamp" = some (.int k) := by
    intro r hr
    obtain ⟨node, hnode⟩ := hchildNode r hr
    obtain ⟨c, hc⟩ := hCovered r node hnode
    obtain ⟨k, hk⟩ := CommentManager.timestampIsInt hDeclares.toDeclaresTypes hManagerWF hc
    exact ⟨c, k, hc, hk⟩
  -- What `expectComment`'s body reads of the environment the call it is let over built.
  have hGlobals : (CommentThread.linearize.callEnv gs
      [Value.struct "CommentThreads" thfvs, manager,
        Value.struct "CommentThread" tfvs]).globals = gs := by
    simp [CommentThread.linearize, FuncDecl.callEnv, Env.extend, Globals.env]
  have hShadow : (CommentThread.linearize.callEnv gs
      [Value.struct "CommentThreads" thfvs, manager,
        Value.struct "CommentThread" tfvs]).bindings.lookup "CommentManager.get" = none := by
    simp [CommentThread.linearize, FuncDecl.callEnv, Env.extend, Globals.env, List.lookup]
  have hManagerBinding : (CommentThread.linearize.callEnv gs
      [Value.struct "CommentThreads" thfvs, manager,
        Value.struct "CommentThread" tfvs]).bindings.lookup "manager" = some manager := by
    simp [CommentThread.linearize, FuncDecl.callEnv, Env.extend, Globals.env, List.lookup]
  -- The two closures the body lets over itself are never stuck, and what they are is their
  -- equations: a `lam` evaluates to the closure and to nothing else.
  refine Stuck.not_let Stuck.not_lam fun ec hec => ?_
  have hecEq := Eval.lam_inv hec
  refine Stuck.not_let Stuck.not_lam fun cf hcf => ?_
  have hcfEq := Eval.lam_inv hcf
  -- The sort over the children: the comparison is the one place a pair of values is compared.
  refine Stuck.not_let (Stuck.not_listSortBy
    (Stuck.not_structGet_varRef (by simp [CommentThread.linearize, FuncDecl.callEnv, Env.extend,
      Globals.env, Env.lookup, List.lookup]) hchField)
    (Stuck.not_varRef (v := cf) (by simp [Env.lookup, List.lookup]))
    (fun v hv => ?_) (fun v hv => ?_)
    (fun vs cb cg ps body hel hfl a ha b hb => ?_)) fun sc hsc => ?_
  · rw [Eval.structGet_varRef_eq (by simp [CommentThread.linearize, FuncDecl.callEnv, Env.extend,
      Globals.env, Env.lookup, List.lookup]) hchField hv]
    exact ⟨_, rfl⟩
  · have hv' := Eval.varRef_inv hv
    simp [Env.lookup, List.lookup, hcfEq] at hv'
    subst hv'
    exact ⟨_, _, _, _, rfl⟩
  · -- one pair of children the sort asked about
    obtain rfl : vs = childRefs := by
      simpa using Eval.structGet_varRef_eq (by simp [CommentThread.linearize, FuncDecl.callEnv,
        Env.extend, Globals.env, Env.lookup, List.lookup]) hchField hel
    obtain ⟨rfl, rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ ∧ _ := by
      simpa [Env.lookup, List.lookup, hcfEq, Env.closure, Value.closure.injEq] using
        Eval.varRef_inv hfl
    obtain ⟨cav, ki, hcaGet, hcai⟩ := hchildStamp a ha
    obtain ⟨cbv, kj, hcbGet, hcbj⟩ := hchildStamp b hb
    exact ⟨.cons "a" (hchildTy a ha) (.cons "b" (hchildTy b hb) .nil),
      CommentThread.linearize.not_stuck_comparisonFunction_body hWellTyped hDeclares.get hGlobals
        hShadow hManagerBinding hManagerWF.hasType (hchildTy a ha) (hchildTy b hb) hcaGet hcbGet
        hcai hcbj (by simp [Env.extend, Env.lookup])
        (by simp [Env.extend, Env.lookup, List.lookup])
        (by simp [Env.extend, Env.lookup, List.lookup, hecEq]),
      fun u hu => Eval.isBool_le hu⟩
  · -- The sort rearranged the children and did nothing else.
    obtain ⟨vs0, cmp, hvs0, rfl⟩ := Eval.listSortBy_inv hsc
    obtain rfl : childRefs = vs0 := by
      simpa using (Eval.structGet_varRef_eq (by simp [CommentThread.linearize, FuncDecl.callEnv,
        Env.extend, Globals.env, Env.lookup, List.lookup]) hchField hvs0).symm
    refine Stuck.not_lcons ?_ ?_ fun v hv => ?_
    · -- the head of the list: the thread's own comment
      refine Stuck.not_app_varRef (by simpa [Env.lookup, List.lookup] using hecEq) ?_ ?_ ?_
      · intro e he
        obtain rfl : e = (Expression.varRef "thread").structGet "value" := by simpa using he
        exact Stuck.not_structGet_varRef (by simp [CommentThread.linearize, FuncDecl.callEnv,
          Env.extend, Globals.env, Env.lookup, List.lookup]) hrootField
      · intro vs hlen hev
        obtain ⟨w, rfl⟩ : ∃ w, vs = [w] := by
          rcases vs with _ | ⟨w, _ | _⟩ <;> simp_all
        obtain rfl := Eval.structGet_varRef_eq (by simp [CommentThread.linearize, FuncDecl.callEnv,
          Env.extend, Globals.env, Env.lookup, List.lookup]) hrootField
          (hev ((Expression.varRef "thread").structGet "value", w) (by simp))
        exact .cons "ref" hrootTy .nil
      · intro vs hlen hev
        obtain ⟨w, rfl⟩ : ∃ w, vs = [w] := by
          rcases vs with _ | ⟨w, _ | _⟩ <;> simp_all
        obtain rfl := Eval.structGet_varRef_eq (by simp [CommentThread.linearize, FuncDecl.callEnv,
          Env.extend, Globals.env, Env.lookup, List.lookup]) hrootField
          (hev ((Expression.varRef "thread").structGet "value", w) (by simp))
        exact CommentThread.linearize.not_stuck_expectComment_body hWellTyped hDeclares.get
          hGlobals hShadow hManagerBinding hManagerWF.hasType hrootTy hrootGet
    · -- the rest of the list: one run per child
      refine Stuck.not_listFlatMap
        (Stuck.not_varRef (v := .list (Value.sortWith cmp childRefs))
          (by simp [Env.lookup, List.lookup]))
        Stuck.not_lam (fun u hu => ?_) (fun u hu => ?_)
        (fun vs cb cg ps body hel hfl w hw => ?_)
      · have hu' := Eval.varRef_inv hu
        simp [Env.lookup, List.lookup] at hu'
        subst hu'
        exact ⟨_, rfl⟩
      · obtain rfl := Eval.lam_inv hu
        exact ⟨_, _, _, _, rfl⟩
      · obtain rfl : vs = Value.sortWith cmp childRefs := by
          have hel' := Eval.varRef_inv hel
          simp [Env.lookup, List.lookup] at hel'
          exact hel'.symm
        obtain ⟨rfl, rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ ∧ _ := by
          simpa [Env.closure, Value.closure.injEq] using Eval.lam_inv hfl
        have hw' : w ∈ childRefs := Value.mem_sortWith.mp hw
        obtain ⟨node, hnode⟩ := hchildNode w hw'
        exact ⟨.cons "childRef" (hchildTy w hw') .nil,
          CommentThread.linearize.not_stuck_childBody (kvs := kvs) hDeclares.linearize
            (by simp [CommentThread.linearize, FuncDecl.callEnv, Env.extend, Globals.env])
            (by simp [CommentThread.linearize, FuncDecl.callEnv, Env.extend, Globals.env,
              List.lookup])
            (by simp [CommentThread.linearize, FuncDecl.callEnv, Env.extend, Globals.env,
              List.lookup])
            (by simp [CommentThread.linearize, FuncDecl.callEnv, Env.extend, Globals.env,
              List.lookup])
            (by simp [Env.extend]) hmfield hThreadsWF.hasType hManagerWF.hasType
            (CommentThreads.hasType_node? hDeclares.toDeclaresTypes hThreadsWF hnode) hnode
            (ih node ⟨tref, childRefs, w, htref, hchField, hw', hnode⟩ ⟨w, hnode⟩),
          fun u hu => CommentThread.linearize.isList_childBody hWellTyped hDeclares.linearize
            (by simp [CommentThread.linearize, FuncDecl.callEnv, Env.extend, Globals.env])
            (by simp [CommentThread.linearize, FuncDecl.callEnv, Env.extend, Globals.env,
              List.lookup]) hu⟩
    · obtain ⟨_, _, _, _, _, _, -, -, -, -, rfl⟩ := Eval.listFlatMap_inv hv
      exact ⟨_, rfl⟩

/-! ## Progress for `nextCommentInThread`

`Progress` (Lang/Progress.lean) stated of one declaration, and then strengthened past it.  `¬Stuck`
over the body under the environment a call builds is the general property read off this
declaration: nothing it evaluates reaches a form no rule of `Eval` can fire on.  It is silent about
the two other ways an expression has no value — divergence, and an `unreachable` reached — so the
second conjunct says a call has a value after all, which is where the model's invariants are spent.

`Eval` has no rule for `unreachable` (`Eval.not_unreachable`), so a derivation of a value for the
body is itself the proof that neither `unreachable` in it was evaluated: "the unreachables are not
reachable" needs no separate statement, and there is nothing weaker that could be said about them —
an `unreachable` is reached or the call has a value.

Neither conjunct implies the other.  Nothing here proves `Eval` deterministic, so a value by one
derivation does not rule out a `Stuck` derivation whose mismatch premise gives a subexpression some
other value; and `¬Stuck` holds of a body stopped at an `unreachable`. -/

/-- The first conjunct: nothing in the body goes wrong.

Eight `let`s walked with `Stuck.not_let`, one form at a time.  The bound expression of each is
refuted by the lemma for its form, and the body of each by the same walk one level in — under an
environment binding the name to *whatever* value the `let`'s expression produced, which is why every
level starts by reading that value off the expression.  Where the expression is a `varRef`, a `lam`
or a field read of one, the reading is an inversion principle; where it is a call, it is the
declaration's result type through `FuncDecl.Apply.hasType`.

Nothing here needs the two `unreachable`s to be unreachable: `Stuck.not_optionMatch_unreachable`
refutes the branch that reaches one by `Stuck.not_unreachable`, whatever the scrutinee did.  What
the index and the length have to be is only that they are `int`s, which is what the arithmetic
forms ask of their operands. -/
private theorem CommentThreads.nextCommentInThread.not_stuck_body {td : TypeDecls} {gs : Globals}
    {threads manager selection thread ref rootRef : Value}
    (hWellTyped : Globals.WellTyped td gs)
    (hDeclares : Model.Declares td gs)
    (hThreadsWF : CommentThreads.WellFormed td threads)
    (hManagerWF : CommentManager.WellFormed td manager)
    (hCovered : CommentThreads.NodesCovered manager threads)
    (hSelection : selection.HasType td (.struct "SelectedComment"))
    (hThread : selection.field? "thread" = some thread)
    (hRef : selection.field? "comment" = some ref)
    (hNode : CommentThreads.node? threads rootRef = some thread) :
    ¬Stuck td (CommentThreads.nextCommentInThread.callEnv gs [threads, manager, selection])
      CommentThreads.nextCommentInThread.body := by
  -- The selection's three fields, at the types `SelectedComment` declares for them.
  obtain ⟨ver, hverField, -⟩ := Value.hasType_field hSelection hDeclares.selectedComment
    (f := "version") (t := .ind "FileVersion") rfl
  have hrefTy : ref.HasType td (.struct "CommentRef") := by
    obtain ⟨w, hw, hwTy⟩ := Value.hasType_field hSelection hDeclares.selectedComment
      (f := "comment") (t := .struct "CommentRef") rfl
    obtain rfl : w = ref := Option.some.inj (hw.symm.trans hRef)
    exact hwTy
  have hthreadTy : thread.HasType td (.struct "CommentThread") :=
    CommentThreads.hasType_node? hDeclares.toDeclaresTypes hThreadsWF hNode
  have hsel : (CommentThreads.nextCommentInThread.callEnv gs
      [threads, manager, selection]).lookup "selection" = some selection := by
    simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
      List.lookup]
  -- `selection.thread`: the thread this call linearizes.
  refine Stuck.not_let (Stuck.not_structGet_varRef hsel hThread) fun v₁ hv₁ => ?_
  rw [Eval.structGet_varRef_eq hsel hThread hv₁]
  -- The call to `linearize`, not stuck by its own progress.
  refine Stuck.not_let (by
    refine Stuck.not_app_global (d := CommentThread.linearize)
      (by simpa [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend,
        Globals.env] using hDeclares.linearize)
      (by simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env,
        List.lookup]) ?_ ?_ ?_
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact Stuck.not_varRef (v := threads) (by simp [CommentThreads.nextCommentInThread,
          FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup, List.lookup])
      · exact Stuck.not_varRef (v := manager) (by simp [CommentThreads.nextCommentInThread,
          FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup, List.lookup])
      · exact Stuck.not_varRef (v := thread) (by simp [Env.lookup, List.lookup])
    · intro vs hlen hev
      obtain ⟨x, y, z, rfl⟩ : ∃ x y z, vs = [x, y, z] := by
        rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | _⟩⟩⟩ <;> simp_all
      have hx := Eval.varRef_inv (hev (Expression.varRef "threads", x) (by simp))
      have hy := Eval.varRef_inv (hev (Expression.varRef "manager", y) (by simp))
      have hz := Eval.varRef_inv (hev (Expression.varRef "selectedThread", z) (by simp))
      simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env,
        Env.lookup, List.lookup] at hx hy hz
      subst hx
      subst hy
      subst hz
      exact .cons "threads" hThreadsWF.hasType
        (.cons "manager" hManagerWF.hasType (.cons "thread" hthreadTy .nil))
    · intro vs hlen hev
      obtain ⟨x, y, z, rfl⟩ : ∃ x y z, vs = [x, y, z] := by
        rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | _⟩⟩⟩ <;> simp_all
      have hx := Eval.varRef_inv (hev (Expression.varRef "threads", x) (by simp))
      have hy := Eval.varRef_inv (hev (Expression.varRef "manager", y) (by simp))
      have hz := Eval.varRef_inv (hev (Expression.varRef "selectedThread", z) (by simp))
      simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env,
        Env.lookup, List.lookup] at hx hy hz
      subst hx
      subst hy
      subst hz
      simpa [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env] using
        CommentThread.linearize.not_stuck_body hWellTyped hDeclares hThreadsWF hManagerWF hCovered
          hNode) fun v₂ hv₂ => ?_
  -- What that call returned is a list of comments, by the result type `linearize` declares.
  obtain ⟨vs₂, -, -, happly₂⟩ :=
    FuncDecl.apply_of_eval_app
      (by simpa [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend,
        Globals.env] using hDeclares.linearize)
      (by simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env,
        List.lookup]) hv₂
  have happly₂' : CommentThread.linearize.Apply td gs vs₂ v₂ := by
    simpa [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env] using
      happly₂
  obtain ⟨cs, rfl, hcsTy⟩ := Value.eq_list_of_hasType
    (happly₂'.hasType hWellTyped (hWellTyped _ _ hDeclares.linearize))
  -- The mapping that reads each comment's ref.
  refine Stuck.not_let (by
    refine Stuck.not_listMap
      (Stuck.not_varRef (v := Value.list cs) (by simp [Env.lookup, List.lookup]))
      Stuck.not_lam (fun u hu => ?_) (fun u hu => ?_)
      (fun vs cb cg ps body hel hfl w hw => ?_)
    · have hu' := Eval.varRef_inv hu
      simp [Env.lookup, List.lookup] at hu'
      subst hu'
      exact ⟨_, rfl⟩
    · obtain rfl := Eval.lam_inv hu
      exact ⟨_, _, _, _, rfl⟩
    · obtain rfl : cs = vs := by
        have hel' := Eval.varRef_inv hel
        simp [Env.lookup, List.lookup] at hel'
        simpa using hel'
      obtain ⟨rfl, rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ ∧ _ := by
        simpa [Env.closure, Value.closure.injEq] using Eval.lam_inv hfl
      obtain ⟨rv, hrv, -⟩ := Value.hasType_field (hcsTy w hw) hDeclares.comment
        (f := "ref") (t := .struct "CommentRef") rfl
      exact ⟨.cons "c" (hcsTy w hw) .nil,
        Stuck.not_structGet_varRef (by simp [Env.extend, Env.lookup]) hrv⟩) fun v₃ hv₃ => ?_
  -- And what *it* returned is one ref per comment, each a `CommentRef`.
  obtain ⟨cs', refs, cb₃, cg₃, ps₃, body₃, hel₃, hfl₃, hlen₃, hev₃, rfl⟩ := Eval.listMap_inv hv₃
  obtain rfl : cs = cs' := by
    have h := Eval.varRef_inv hel₃
    simp [Env.lookup, List.lookup] at h
    simpa using h
  obtain ⟨rfl, rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ ∧ _ := by
    simpa [Env.closure, Value.closure.injEq] using Eval.lam_inv hfl₃
  have hrefsField : ∀ p ∈ cs.zip refs, p.1.field? "ref" = some p.2 := by
    intro p hp
    obtain ⟨name, fvs, hc, hf⟩ := Eval.structGet_inv (hev₃ p hp)
    have hcv := Eval.varRef_inv hc
    simp [Env.extend, Env.lookup] at hcv
    rw [hcv]
    simpa [Value.field?] using hf
  have hrefsTy : ∀ w ∈ refs, w.HasType td (.struct "CommentRef") := by
    intro w hw
    obtain ⟨c, hp⟩ := exists_mem_zip_of_mem_right hlen₃ hw
    obtain ⟨rv, hrv, hrvTy⟩ := Value.hasType_field (hcsTy c (List.of_mem_zip hp).1)
      hDeclares.comment (f := "ref") (t := .struct "CommentRef") rfl
    obtain rfl : rv = w := Option.some.inj (hrv.symm.trans (hrefsField (c, w) hp))
    exact hrvTy
  -- `selection.comment`: the ref the search looks for.
  refine Stuck.not_let (Stuck.not_structGet_varRef (by
    simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
      List.lookup]) hRef) fun v₄ hv₄ => ?_
  rw [Eval.structGet_varRef_eq (by simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv,
    Env.extend, Globals.env, Env.lookup, List.lookup]) hRef hv₄]
  -- The predicate the search runs, and the search itself.
  refine Stuck.not_let Stuck.not_lam fun mf hmf => ?_
  have hmfEq := Eval.lam_inv hmf
  refine Stuck.not_let (by
    refine Stuck.not_optionMatch_unreachable ?_ (fun u hu => Eval.isOption_listFindIndex hu)
      fun w hw => Stuck.not_varRef (v := w) (by simp [Env.lookup, List.lookup])
    refine Stuck.not_listFindIndex
      (Stuck.not_varRef (v := Value.list refs) (by simp [Env.lookup, List.lookup]))
      (Stuck.not_varRef (v := mf) (by simp [Env.lookup, List.lookup]))
      (fun u hu => ?_) (fun u hu => ?_) (fun vs cb cg ps body hel hfl w hw => ?_)
    · have hu' := Eval.varRef_inv hu
      simp [Env.lookup, List.lookup] at hu'
      subst hu'
      exact ⟨_, rfl⟩
    · have hu' := Eval.varRef_inv hu
      simp [Env.lookup, List.lookup, hmfEq] at hu'
      subst hu'
      exact ⟨_, _, _, _, rfl⟩
    · obtain rfl : refs = vs := by
        have hel' := Eval.varRef_inv hel
        simp [Env.lookup, List.lookup] at hel'
        simpa using hel'
      obtain ⟨rfl, rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ ∧ _ := by
        simpa [Env.lookup, List.lookup, hmfEq, Env.closure, Value.closure.injEq] using
          Eval.varRef_inv hfl
      refine ⟨.cons "ref" (hrefsTy w hw) .nil, ?_, fun u hu => Eval.isBool_equals hu⟩
      refine Stuck.not_equals (Stuck.not_varRef (v := w) (by simp [Env.extend, Env.lookup]))
        (Stuck.not_varRef (v := ref) (by simp [Env.extend, Env.lookup, List.lookup]))
        fun u₁ u₂ h₁ h₂ => ?_
      have h₁' := Eval.varRef_inv h₁
      have h₂' := Eval.varRef_inv h₂
      simp [Env.extend, Env.lookup, List.lookup] at h₁' h₂'
      subst h₁'
      subst h₂'
      obtain ⟨b, hb, -⟩ := CommentRef.beq?_eq_some hDeclares.commentRef (hrefsTy w hw) hrefTy
      simp [hb]) fun v₆ hv₆ => ?_
  -- What the search answered is an index, which is all the arithmetic below asks of it.
  obtain ⟨w₆, hscrut₆, hbound₆⟩ := Eval.optionMatch_unreachable_inv hv₆
  have hb₆ := Eval.varRef_inv hbound₆
  simp [Env.lookup, List.lookup] at hb₆
  subst hb₆
  obtain ⟨k, rfl⟩ : ∃ k : Int, w₆ = .int k := by
    obtain ⟨vs₆, cb₆, cg₆, ps₆, body₆, hel₆, -, hcase⟩ := Eval.listFindIndex_inv hscrut₆
    rcases hcase with ⟨pre, wsel, post, -, -, -, hval⟩ | ⟨-, hval⟩
    · exact ⟨(pre.length : Int), by simpa using hval⟩
    · simp at hval
  -- The index of the next comment: arithmetic over that index and the list's length.
  refine Stuck.not_let (by
    refine Stuck.not_min ?_ ?_ (fun u hu => ?_) (fun u hu => ?_)
    · refine Stuck.not_plus (Stuck.not_varRef (v := Value.int k) (by simp [Env.lookup,
        List.lookup])) Stuck.not_intLit (fun u hu => ?_) (fun u hu => ?_)
      · have hu' := Eval.varRef_inv hu
        simp [Env.lookup, List.lookup] at hu'
        subst hu'
        exact ⟨_, rfl⟩
      · rw [Eval.intLit_inv hu]
        exact ⟨_, rfl⟩
    · refine Stuck.not_minus (Stuck.not_listLength (Stuck.not_varRef (v := Value.list refs)
        (by simp [Env.lookup, List.lookup])) (fun u hu => ?_)) Stuck.not_intLit
        (fun u hu => ?_) (fun u hu => ?_)
      · have hu' := Eval.varRef_inv hu
        simp [Env.lookup, List.lookup] at hu'
        subst hu'
        exact ⟨_, rfl⟩
      · obtain ⟨-, -, rfl⟩ := Eval.listLength_inv hu
        exact ⟨_, rfl⟩
      · rw [Eval.intLit_inv hu]
        exact ⟨_, rfl⟩
    · obtain ⟨-, -, -, -, rfl⟩ := Eval.plus_inv hu
      exact ⟨_, rfl⟩
    · obtain ⟨-, -, -, -, rfl⟩ := Eval.minus_inv hu
      exact ⟨_, rfl⟩) fun v₇ hv₇ => ?_
  obtain ⟨n, rfl⟩ : ∃ n : Int, v₇ = .int n := by
    obtain ⟨-, -, -, -, rfl⟩ := Eval.min_inv hv₇
    exact ⟨_, rfl⟩
  -- The ref at that index.
  refine Stuck.not_let (by
    refine Stuck.not_optionMatch_unreachable
      (Stuck.not_listIndex
        (Stuck.not_varRef (v := Value.list refs) (by simp [Env.lookup, List.lookup]))
        (Stuck.not_varRef (v := Value.int n) (by simp [Env.lookup, List.lookup]))
        (fun u hu => ?_) (fun u hu => ?_))
      (fun u hu => Eval.isOption_listIndex hu)
      fun w hw => Stuck.not_varRef (v := w) (by simp [Env.lookup, List.lookup])
    · have hu' := Eval.varRef_inv hu
      simp [Env.lookup, List.lookup] at hu'
      subst hu'
      exact ⟨_, rfl⟩
    · have hu' := Eval.varRef_inv hu
      simp [Env.lookup, List.lookup] at hu'
      subst hu'
      exact ⟨_, rfl⟩) fun v₈ hv₈ => ?_
  -- And the selection it answers with, which is stuck exactly where one of its fields is.
  refine Stuck.not_structNew fun p hp => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact Stuck.not_structGet_varRef (by simp [CommentThreads.nextCommentInThread,
      FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup, List.lookup]) hverField
  · exact Stuck.not_structGet_varRef (by simp [CommentThreads.nextCommentInThread,
      FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup, List.lookup]) hThread
  · exact Stuck.not_varRef (v := v₈) (by simp [Env.lookup, List.lookup])

/-- The second conjunct: a call has a value, which is where the two `unreachable`s are paid for.

`Eval` has no rule for the form, so building a derivation *is* showing neither branch that reaches
one is taken.  The search finds an index because the selected ref occurs among the refs of the
linearized thread — `CommentThread.linearize_hasAllThreadComments` at `ref`, with
`hManagerWF.refMatchesKey` to turn the comment the manager holds back into the ref the mapping read
off it — and `exists_first_of_mem` is what turns that into the split `Eval.EListFindIndexSome`
needs.  The index read finds an element because `min (i + 1) (length - 1)` is in range once an index
was found at all, which is the one step of this proof that is arithmetic rather than invariant.

`CommentRef.beq?_eq_some` is what the `==` costs, three times over: it has an answer at all, it is
`false` at every ref before the selected one, and it is `true` at the selected one. -/
private theorem CommentThreads.nextCommentInThread.apply_exists {td : TypeDecls} {gs : Globals}
    {threads manager selection thread ref rootRef : Value}
    (hWellTyped : Globals.WellTyped td gs)
    (hDeclares : Model.Declares td gs)
    (hThreadsWF : CommentThreads.WellFormed td threads)
    (hManagerWF : CommentManager.WellFormed td manager)
    (hCovered : CommentThreads.NodesCovered manager threads)
    (hSelection : selection.HasType td (.struct "SelectedComment"))
    (hThread : selection.field? "thread" = some thread)
    (hRef : selection.field? "comment" = some ref)
    (hNode : CommentThreads.node? threads rootRef = some thread)
    (hHasRef : CommentThread.HasRef threads thread ref) :
    ∃ v, CommentThreads.nextCommentInThread.Apply td gs [threads, manager, selection] v := by
  obtain ⟨ver, hverField, -⟩ := Value.hasType_field hSelection hDeclares.selectedComment
    (f := "version") (t := .ind "FileVersion") rfl
  have hrefTy : ref.HasType td (.struct "CommentRef") := by
    obtain ⟨w, hw, hwTy⟩ := Value.hasType_field hSelection hDeclares.selectedComment
      (f := "comment") (t := .struct "CommentRef") rfl
    obtain rfl : w = ref := Option.some.inj (hw.symm.trans hRef)
    exact hwTy
  -- The selection as a struct *value*: this body reads its fields rather than being handed them.
  obtain ⟨selfvs, rfl⟩ := Value.eq_struct_of_hasType hSelection
  have hverF : selfvs.lookup "version" = some ver := by simpa [Value.field?] using hverField
  have hthreadF : selfvs.lookup "thread" = some thread := by simpa [Value.field?] using hThread
  have hrefF : selfvs.lookup "comment" = some ref := by simpa [Value.field?] using hRef
  -- The linearized thread, and the comments it holds.
  obtain ⟨cs, happly⟩ :=
    CommentThread.linearize.apply_exists hDeclares hThreadsWF hManagerWF hCovered hNode
  have hcsTy : ∀ w ∈ cs, w.HasType td (.struct "Comment") := by
    cases happly.hasType hWellTyped (hWellTyped _ _ hDeclares.linearize) with
    | list h => exact h
  -- One ref per comment: the list the mapping produces, built from one witness per element.
  obtain ⟨refs, hrlen, hrall⟩ := exists_zip_of_forall_exists (l := cs)
    (P := fun (c r : Value) => c.field? "ref" = some r)
    fun c hc => by
      obtain ⟨rv, hrv, -⟩ := Value.hasType_field (hcsTy c hc) hDeclares.comment
        (f := "ref") (t := .struct "CommentRef") rfl
      exact ⟨rv, hrv⟩
  have hrefsTy : ∀ w ∈ refs, w.HasType td (.struct "CommentRef") := by
    intro w hw
    obtain ⟨c, hp⟩ := exists_mem_zip_of_mem_right hrlen hw
    obtain ⟨rv, hrv, hrvTy⟩ := Value.hasType_field (hcsTy c (List.of_mem_zip hp).1)
      hDeclares.comment (f := "ref") (t := .struct "CommentRef") rfl
    obtain rfl : rv = w := Option.some.inj (hrv.symm.trans (hrall (c, w) hp))
    exact hrvTy
  -- The selected ref is one of them, which is what rules out the first `unreachable`.
  obtain ⟨c₀, hget₀, hmem₀⟩ :=
    CommentThread.linearize_hasAllThreadComments hDeclares happly ref hHasRef
  have hrefMem : ref ∈ refs := by
    obtain ⟨r₀, hp₀⟩ := exists_mem_zip_of_mem_left hrlen hmem₀
    obtain rfl : r₀ = ref := Option.some.inj
      ((hrall (c₀, r₀) hp₀).symm.trans (hManagerWF.refMatchesKey ref c₀ hget₀))
    exact (List.of_mem_zip hp₀).2
  obtain ⟨pre, wsel, post, hsplit, hpre, hwsel⟩ :=
    exists_first_of_mem (fun y => y = ref) hrefMem rfl
  rw [hwsel] at hsplit
  have hlen : refs.length = pre.length + 1 + post.length := by
    rw [hsplit, List.length_append, List.length_cons]
    omega
  -- A found index and a non-empty list put the next index in range: the second `unreachable`.
  obtain ⟨rfinal, hrfinal⟩ : ∃ r, Value.index? refs
      (min ((pre.length : Int) + 1) ((refs.length : Int) - 1)) = some r := by
    have h0 : ¬min ((pre.length : Int) + 1) ((refs.length : Int) - 1) < 0 := by omega
    have hidx : (min ((pre.length : Int) + 1) ((refs.length : Int) - 1)).toNat < refs.length := by
      omega
    exact ⟨refs[(min ((pre.length : Int) + 1) ((refs.length : Int) - 1)).toNat],
      by simp [Value.index?, h0]⟩
  -- The selection the call answers with: the one it was given, at the ref the index found.
  refine ⟨.struct "SelectedComment" [("version", ver), ("thread", thread), ("comment", rfinal)],
    .EApply _ (.cons "threads" hThreadsWF.hasType
      (.cons "manager" hManagerWF.hasType (.cons "selection" hSelection .nil))) ?_⟩
  refine Eval.ELet _ _ _ (Eval.EStructGet (name := "SelectedComment") _ _ (Eval.EVarRef _ (by
    simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
      List.lookup])) hthreadF) ?_
  refine Eval.ELet _ _ _ (FuncDecl.eval_app_of_apply (x := "CommentThread.linearize")
    (by simpa [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend,
      Globals.env] using hDeclares.linearize)
    (by simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env,
      List.lookup]) rfl ?args
    (by simpa [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend,
      Globals.env] using happly)) ?_
  case args =>
    intro p hp
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact Eval.EVarRef _ (by simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv,
        Env.extend, Globals.env, Env.lookup, List.lookup])
    · exact Eval.EVarRef _ (by simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv,
        Env.extend, Globals.env, Env.lookup, List.lookup])
    · exact Eval.EVarRef _ (by simp [Env.lookup, List.lookup])
  refine Eval.ELet _ _ _ (Eval.EListMap _ _ (Eval.EVarRef _ (by simp [Env.lookup, List.lookup]))
    (Eval.ELam _ _) hrlen ?argTys ?calls) ?_
  case argTys =>
    intro p hp
    exact .cons "c" (hcsTy p.1 (List.of_mem_zip hp).1) .nil
  case calls =>
    intro p hp
    obtain ⟨cfvs, hcfvs⟩ := Value.eq_struct_of_hasType (hcsTy p.1 (List.of_mem_zip hp).1)
    have hf : cfvs.lookup "ref" = some p.2 := by
      have h := hrall p hp
      rw [hcfvs] at h
      simpa [Value.field?] using h
    rw [hcfvs]
    exact Eval.EStructGet (name := "Comment") _ _
      (Eval.EVarRef _ (by simp [Env.extend, Env.lookup])) hf
  refine Eval.ELet _ _ _ (Eval.EStructGet (name := "SelectedComment") _ _ (Eval.EVarRef _ (by
    simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
      List.lookup])) hrefF) ?_
  refine Eval.ELet _ _ _ (Eval.ELam _ _) ?_
  refine Eval.ELet (v₁ := Value.int (pre.length : Int)) _ _ _
    (Eval.EOptionMatchSome (w := Value.int (pre.length : Int)) _ _ _ _ ?search
      (Eval.EVarRef _ (by simp [Env.lookup, List.lookup]))) ?_
  case search =>
    refine Eval.EListFindIndexSome (pre := pre) (w := ref) (post := post) _ _
      (Eval.EVarRef _ (by rw [← hsplit]; simp [Env.lookup, List.lookup])) (Eval.EVarRef _ rfl)
      ?preTys ?preEv (.cons "ref" hrefTy .nil) ?selEv
    case preTys =>
      intro u hu
      exact .cons "ref" (hrefsTy u (by rw [hsplit]; simp [hu])) .nil
    case preEv =>
      intro u hu
      obtain ⟨b, hb, hiff⟩ := CommentRef.beq?_eq_some hDeclares.commentRef
        (hrefsTy u (by rw [hsplit]; simp [hu])) hrefTy
      obtain rfl : b = false := by
        cases b with
        | false => rfl
        | true => exact absurd (hiff.mp rfl) (hpre u hu)
      exact Eval.EEquals _ _ (Eval.EVarRef _ (by simp [Env.extend, Env.lookup]))
        (Eval.EVarRef _ (by simp [Env.extend, Env.lookup, List.lookup])) hb
    case selEv =>
      obtain ⟨b, hb, hiff⟩ := CommentRef.beq?_eq_some hDeclares.commentRef hrefTy hrefTy
      obtain rfl : b = true := hiff.mpr rfl
      exact Eval.EEquals _ _ (Eval.EVarRef _ (by simp [Env.extend, Env.lookup]))
        (Eval.EVarRef _ (by simp [Env.extend, Env.lookup, List.lookup])) hb
  refine Eval.ELet (v₁ := Value.int (min ((pre.length : Int) + 1) ((refs.length : Int) - 1)))
    _ _ _
    (Eval.EMin _ _
      (Eval.EPlus _ _ (Eval.EVarRef _ (by simp [Env.lookup, List.lookup])) (Eval.EIntLit _))
      (Eval.EMinus _ _ (Eval.EListLength _ (Eval.EVarRef _ (by simp [Env.lookup, List.lookup])))
        (Eval.EIntLit _))) ?_
  refine Eval.ELet (v₁ := rfinal) _ _ _
    (Eval.EOptionMatchSome (w := rfinal) _ _ _ _
      (by
        rw [← hrfinal]
        exact Eval.EListIndex _ _ (Eval.EVarRef _ (by simp [Env.lookup, List.lookup]))
          (Eval.EVarRef _ (by simp [Env.lookup, List.lookup])))
      (Eval.EVarRef _ (by simp [Env.lookup, List.lookup]))) ?_
  refine Eval.EStructNew _ _ rfl ?_
  intro p hp
  simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact Eval.EStructGet (name := "SelectedComment") _ _ (Eval.EVarRef _ (by
      simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env,
        Env.lookup, List.lookup])) hverF
  · exact Eval.EStructGet (name := "SelectedComment") _ _ (Eval.EVarRef _ (by
      simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env,
        Env.lookup, List.lookup])) hthreadF
  · exact Eval.EVarRef _ (by simp [Env.lookup, List.lookup])

/-- `nextCommentInThread` never goes wrong and always answers: no subexpression of its body is
stuck, and a call to it has a value — so neither `unreachable` in it is reached, and the recursion
`CommentThread.linearize` makes terminates.

The first group of hypotheses is what progress alone needs.  `hDeclares` and `hWellTyped` make the
`varRef`s resolve and keep the values flowing through the body well typed — the call to
`CommentThread.linearize` is checked against `gs`, and so is the call to `CommentManager.get` its
body makes in turn.  `hDeclares` also lets the field reads be read at their declared types:
`selection.thread` is a `CommentThread`, which is what the call to `linearize` needs of its third
argument, and `c.ref` is a `CommentRef`, which is what makes the `==` the search runs have an
answer.

The rest is what the second conjunct costs, one hypothesis per `unreachable` reachable without it:

* `hThreadsWF.childrenRegistered` and `hCovered` are `linearize`'s two — a child ref with no node,
  and a node naming a comment the manager does not hold — and `hNode` is what puts the selected
  thread in range of both, since `CommentThreads.NodesCovered` speaks of registered nodes only.
  `hThreadsWF.childEdgeWf` is what makes the recursion over the children well founded, and
  `hManagerWF` is what gives each comment the sort's comparison a timestamp to compare
  (`CommentManager.timestampIsInt`).
* `hHasRef` is this body's own: the selected ref has to occur in the linearized thread for the
  search to find an index, which is `CommentThread.linearize_hasAllThreadComments` at `ref`,
  together with `hManagerWF.refMatchesKey` to turn the comment the manager holds back into the ref
  the map of the result carries.

The index read needs nothing further: a found index is in range and the list is non-empty, so
`min (i + 1) (length - 1)` is in range too, which is the second `unreachable` ruled out by
arithmetic rather than by an invariant. -/
theorem CommentThreads.nextCommentInThread.progress {td : TypeDecls} {gs : Globals}
    {threads manager selection thread ref rootRef : Value}
    (hDeclares : Model.Declares td gs)
    (hWellTyped : Globals.WellTyped td gs)
    (hThreadsWF : CommentThreads.WellFormed td threads)
    (hManagerWF : CommentManager.WellFormed td manager)
    (hCovered : CommentThreads.NodesCovered manager threads)
    (hSelection : selection.HasType td (.struct "SelectedComment"))
    (hThread : selection.field? "thread" = some thread)
    (hRef : selection.field? "comment" = some ref)
    (hNode : CommentThreads.node? threads rootRef = some thread)
    (hHasRef : CommentThread.HasRef threads thread ref) :
    ¬Stuck td (CommentThreads.nextCommentInThread.callEnv gs [threads, manager, selection])
        CommentThreads.nextCommentInThread.body ∧
      ∃ v, CommentThreads.nextCommentInThread.Apply td gs [threads, manager, selection] v :=
  ⟨CommentThreads.nextCommentInThread.not_stuck_body hWellTyped hDeclares hThreadsWF hManagerWF
      hCovered hSelection hThread hRef hNode,
    CommentThreads.nextCommentInThread.apply_exists hWellTyped hDeclares hThreadsWF hManagerWF
      hCovered hSelection hThread hRef hNode hHasRef⟩

end
