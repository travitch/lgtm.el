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

/-! ## Helpers over values

A value typed as a struct or as a list is, in fact, one: canonical forms over `Value.HasType`, read
as existentials rather than as the `Value.hasType_*_iff` lemmas' equations, so a forward proof that
only has an abstract `v : Value` and a `v.HasType ...` in hand can replace `v` by the literal shape
`Eval`'s rules need to pattern-match on — `Eval.EStructGet` and friends ask for `Eval td env e
(.struct name fvs)`, not for `v.HasType td (.struct name)`, and no inversion principle here has had
to bridge the two before: every one of them is handed a value already known to be shaped like this,
by the `Eval` it inverts. -/

private theorem Value.eq_struct_of_hasType {td : TypeDecls} {v : Value} {name : String}
    (hv : v.HasType td (.struct name)) : ∃ fvs, v = .struct name fvs := by
  cases hv with
  | struct _ _ _ => exact ⟨_, rfl⟩

private theorem Value.eq_list_of_hasType {td : TypeDecls} {v : Value} {t : Ty}
    (hv : v.HasType td (.list t)) : ∃ vs, v = .list vs ∧ ∀ w ∈ vs, w.HasType td t := by
  cases hv with
  | list hall => exact ⟨_, rfl, hall⟩

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

/-- The dual of `CommentManager.get.eq_get?`: a comment the manager holds under `ref` is what a call
to `CommentManager.get` on `ref` evaluates to.  Where that lemma drops the `ArgsHaveType` premise as
every inversion principle here does, this one has to produce it — a call it builds rather than takes
apart needs its arguments to fit — which is the one way this needs more than `get?`'s equation: a
typing fact about `manager` and about `ref` themselves, had wherever this is used from the thread
and manager invariants already in hand.

No extra comparability side condition appears: `CommentManager.get?` is `Value.lookupField?`, which
is `(KeyValues.lookup? kvs k).join`, so `get? manager ref = some c` already forces
`KeyValues.lookup? kvs k = some (some c)` — exactly what `Eval.EHashmapGet`'s third premise wants. -/
theorem CommentManager.get.apply_of_get? {td : TypeDecls} {gs : Globals} {manager ref c : Value}
    (hmanager : manager.HasType td (.struct "CommentManager"))
    (href : ref.HasType td (.struct "CommentRef"))
    (h : CommentManager.get? manager ref = some c) :
    CommentManager.get.Apply td gs [manager, ref] (.option (some c)) := by
  obtain ⟨fvs, rfl⟩ := Value.eq_struct_of_hasType hmanager
  obtain ⟨kvs, hkvs, hlookup⟩ : ∃ kvs, fvs.lookup "comments" = some (.hashmap kvs) ∧
      KeyValues.lookup? kvs ref = some (some c) := by
    simp only [CommentManager.get?, Value.lookupField?, Value.field?] at h
    cases hfc : fvs.lookup "comments" with
    | none => simp [hfc] at h
    | some w =>
      cases w with
      | hashmap kvs => exact ⟨kvs, by simp, by simpa [hfc, Option.join_eq_some_iff] using h⟩
      | _ => simp [hfc] at h
  refine .EApply _ (.cons "manager" hmanager (.cons "ref" href .nil)) ?_
  have hm : Eval td ((CommentManager.get).callEnv gs [.struct "CommentManager" fvs, ref])
      (.varRef "manager") (.struct "CommentManager" fvs) :=
    Eval.EVarRef _ (by
      simp [CommentManager.get, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup])
  have hk : Eval td ((CommentManager.get).callEnv gs [.struct "CommentManager" fvs, ref])
      (.varRef "ref") ref :=
    Eval.EVarRef _ (by
      simp [CommentManager.get, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
        List.lookup])
  exact Eval.EHashmapGet _ _ (Eval.EStructGet _ _ hm hkvs) hk hlookup


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
    (hLinearize : gs.lookup "CommentThread.linearize" =
      some CommentThread.linearize)
    (hGet : gs.lookup "CommentManager.get" = some CommentManager.get)
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
            Globals.env] using hGet)
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
            Globals.env] using hLinearize)
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

theorem CommentThread.linearize_hasAllThreadComments {td : TypeDecls} {gs : Globals}
    {threads manager thread : Value} {comments : List Value}
    (hLinearize : gs.lookup "CommentThread.linearize" = some CommentThread.linearize)
    (hGet : gs.lookup "CommentManager.get" = some CommentManager.get)
    (h : CommentThread.linearize.Apply td gs [threads, manager, thread] (.list comments)) :
    ∀ ref, CommentThread.HasRef threads thread ref →
      ∃ c, CommentManager.get? manager ref = some c ∧ c ∈ comments := by
  intro ref hhas
  induction hhas generalizing comments with
  | root hvalue =>
    obtain ⟨root, c, -, hroot, hget, hmem, -, -⟩ :=
      CommentThread.linearize.apply_inv hLinearize hGet h
    obtain rfl := Option.some.inj (hroot.symm.trans hvalue)
    exact ⟨c, hget, hmem⟩
  | child hchildField hchildMem hchildNode hrest ih =>
    obtain ⟨root, c, childRefs, hroot, hget, hmem, hchildren, hkids⟩ :=
      CommentThread.linearize.apply_inv hLinearize hGet h
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
  exact CommentThread.linearize_hasAllThreadComments rfl rfl happly

end
