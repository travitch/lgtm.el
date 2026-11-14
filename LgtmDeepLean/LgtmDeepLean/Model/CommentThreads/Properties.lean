module

public import LgtmDeepLean.Model.Basic.WellFormed
public import LgtmDeepLean.Model.CommentThreads.Operations
public import LgtmDeepLean.Model.Program

/-! # The order `CommentThreads.toThreadsOrdered` returns threads in

What the shallow model proves of `toThreadsOrdered` by unfolding it, proved here of the calls the
relational semantics says it has: each location's group of threads occurs as a contiguous run of the
result, and within a run the threads are in timestamp order.

Every hypothesis the shallow version did not need is one the deep embedding has to say out loud.
`gs` must declare the three names these bodies call, since a `varRef` resolves through the globals
table and nothing says that table is the model's.  And the invariants the shallow `CommentThreads`
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

The three facts about lists this development needs that the library states the other way round. -/

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

/-! ## Reading a comment out of the manager

`CommentManager.get` is one `hashmapGet` over one field, which is exactly what
`CommentManager.get?` is: the declaration and the predicate the invariants are stated over agree,
and this is where they are held against each other. -/

theorem CommentManager.get.eq_get? {td : TypeDecls} {gs : Globals} {manager ref c : Value}
    (h : CommentManager.get.Apply td gs [manager, ref] (.option (some c))) :
    CommentManager.get? manager ref = some c := by
  obtain ⟨-, -, hbody⟩ := h
  obtain ⟨kvs, vk, hm, hk, hlookup⟩ := Eval.hashmapGet_inv hbody
  obtain ⟨_n, _fvs, hs, hf⟩ := Eval.structGet_inv hm
  have hlm := Eval.varRef_inv hs
  have hlk := Eval.varRef_inv hk
  simp [CommentManager.get, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
    List.lookup] at hlm hlk
  subst hlm
  subst hlk
  simp [CommentManager.get?, Value.lookupField?, Value.field?, hf, hlookup]


/-! ## Every location's threads

`asAlist` reads each location's root comments out of the manager, hands the list to
`sortThreadLists`, and sorts what comes back by location.  The sort by location rearranges and
nothing else, so every group in the result is one of those `sortThreadLists` answers — which is what
makes the sortedness within a group a fact about `sortThreadLists` alone. -/

theorem CommentThreads.asAlist.sortThreadLists_apply_of_mem {td : TypeDecls} {gs : Globals}
    {threads manager : Value} {groups : List Value}
    (hSortThreadLists : gs.lookup "CommentThreads.asAlist.sortThreadLists" =
      some CommentThreads.asAlist.sortThreadLists)
    (hGet : gs.lookup "CommentManager.get" = some CommentManager.get)
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
          (by simpa [CommentThreads.asAlist, FuncDecl.callEnv, Env.extend, Globals.env] using hGet)
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
        hSortThreadLists)
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
    (hDeclares : Model.Declares td)
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
    (hSortThreadLists : gs.lookup "CommentThreads.asAlist.sortThreadLists" =
      some CommentThreads.asAlist.sortThreadLists)
    (hGet : gs.lookup "CommentManager.get" = some CommentManager.get)
    (hDeclares : Model.Declares td)
    (hThreadsWF : CommentThreads.WellFormed td threads)
    (hManagerWF : CommentManager.WellFormed td manager)
    (h : CommentThreads.asAlist.Apply td gs [threads, manager] (.list groups)) :
    ∀ group ∈ groups, ∃ loc ts stamps, group = .tuple [loc, .list ts] ∧
      ts.length = stamps.length ∧
      (∀ p ∈ ts.zip stamps, CommentManager.rootTimestamp? manager p.1 = some p.2) ∧
      listIsSortedPredicate stamps := by
  intro group hgroup
  obtain ⟨loc, roots, hroots, happly⟩ :=
    CommentThreads.asAlist.sortThreadLists_apply_of_mem hSortThreadLists hGet h group hgroup
  obtain ⟨ts, stamps, hgeq, hlen, hstamps, hsorted⟩ :=
    CommentThreads.asAlist.sortThreadLists.isSortedByTimestamp hDeclares hThreadsWF hManagerWF
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
    (hAsAlist : gs.lookup "CommentThreads.asAlist" = some CommentThreads.asAlist)
    (hSortThreadLists : gs.lookup "CommentThreads.asAlist.sortThreadLists" =
      some CommentThreads.asAlist.sortThreadLists)
    (hGet : gs.lookup "CommentManager.get" = some CommentManager.get)
    (hDeclares : Model.Declares td)
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
        hAsAlist)
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
    CommentThreads.asAlist.threadLocationsSortedByTimestamp hSortThreadLists hGet hDeclares
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

The three hypotheses above are conditions on the globals table, and `modelProgram` meets all three
by `rfl`: the model declares each of those names under its own name.  So this is the theorem read as
a fact about the model rather than about any table that happens to declare the right things, and it
is what says those hypotheses are not vacuous. -/

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
  exact CommentThreads.toThreadsOrdered.groupsAreSorted rfl rfl rfl Model.declares_modelProgram
    hThreadsWF hManagerWF happly

end
