module

import Std

import all LgtmLean.Basic
import all LgtmLean.Tree

private def commentsAllInSameFileOrAllTopLevel (comments : List Comment) : Prop :=
  (∀ c, c ∈ comments → c.location.isTopLevel) ∨
  (∀ c, c ∈ comments → ∃ loc, c.location = .fileLocation loc ∧ loc.version = .base) ∨
  (∀ c, c ∈ comments → ∃ loc, c.location = .fileLocation loc ∧ loc.version = .current)

private def allCommentsHaveBackendId (comments : List Comment) : Prop := ∀ c, c ∈ comments → c.backendId.isSome

/-- Every parent referenced by a comment in the batch is itself the backend id of some comment in
the batch.  This is needed to look the parent up in `serverCommentIds` while assembling threads. -/
private def allParentsInComments (comments : List Comment) : Prop :=
  ∀ c, c ∈ comments → ∀ parentId, c.parent = some parentId → ∃ c', c' ∈ comments ∧ c'.backendId = some parentId

/-- Every comment in the batch has a distinct `ref`, so no `CommentRef` is ever pushed twice into
`locationRoots`. -/
private def commentRefsNodup (comments : List Comment) : Prop := (comments.map Comment.ref).Nodup

/-- A reply's parent was created strictly before it. This rules out cycles in the batch's `parent`
links, which is needed to show every comment's tree node is reachable from some root. -/
private def parentsCreatedBefore (comments : List Comment) : Prop :=
  ∀ c, c ∈ comments → ∀ parentId, c.parent = some parentId →
    ∀ c', c' ∈ comments → c'.backendId = some parentId → c'.createdTimestamp < c.createdTimestamp

private structure CommentTreeBootstrapState where
  commentTreeNodes : Std.HashMap CommentRef CommentThread
  serverCommentIds : Std.HashMap ServerId CommentRef
  locationRoots : Std.HashMap ThreadLocation (List CommentRef)

private def emptyBootstrapState : CommentTreeBootstrapState := ⟨Std.HashMap.emptyWithCapacity, Std.HashMap.emptyWithCapacity, Std.HashMap.emptyWithCapacity⟩

private def insertSingletonOrAppend (value : α) (current : Option (List α)) : Option (List α) :=
  match current with
  | none => some [value]
  | some values => some (value :: values)

private theorem mem_getD_alter_insertSingletonOrAppend
    (m : Std.HashMap ThreadLocation (List CommentRef)) (k k' : ThreadLocation) (v : CommentRef) (ref : CommentRef) :
    ref ∈ (m.alter k (insertSingletonOrAppend v)).getD k' [] ↔
      (k = k' ∧ ref = v) ∨ ref ∈ m.getD k' [] := by
  rw [Std.HashMap.getD_alter]
  split
  · next hk =>
    have hkk' : k = k' := beq_iff_eq.mp hk
    subst hkk'
    rw [Std.HashMap.getD_eq_getD_getElem?]
    rcases hopt : m[k]? with _ | vs
    · simp [insertSingletonOrAppend]
    · simp [insertSingletonOrAppend, List.mem_cons]
  · next hk =>
    simp only [beq_iff_eq] at hk
    simp [hk]

/-- In an assoc-list with BEq-pairwise-distinct keys, filtering for a given key leaves at most the
one matching entry. -/
private theorem filter_beq_fst_eq_of_pairwise {K V : Type} [BEq K] [EquivBEq K]
    {l : List (K × V)} (hDistinct : l.Pairwise (fun a b => (a.1 == b.1) = false)) (k : K) :
    l.filter (fun p => k == p.1) = [] ∨
      ∃ p, p ∈ l ∧ k == p.1 ∧ l.filter (fun p => k == p.1) = [p] := by
  induction l with
  | nil => exact Or.inl rfl
  | cons p rest ih =>
    rw [List.pairwise_cons] at hDistinct
    by_cases hk : k == p.1
    · right
      refine ⟨p, List.mem_cons_self, hk, ?_⟩
      rw [List.filter_cons, if_pos hk]
      congr 1
      rw [List.filter_eq_nil_iff]
      intro q hq hcontra
      exact absurd (BEq.trans (BEq.symm hk) hcontra) (Bool.eq_false_iff.mp (hDistinct.1 q hq))
    · rw [List.filter_cons, if_neg hk]
      rcases ih hDistinct.2 with h | ⟨p', hp', hkp', heq⟩
      · exact Or.inl h
      · exact Or.inr ⟨p', List.mem_cons_of_mem p hp', hkp', heq⟩

private theorem flatMap_snd_filter_beq_fst_toList_eq_getD
    (m : Std.HashMap ThreadLocation (List CommentRef)) (k : ThreadLocation) :
    (m.toList.filter (fun p => k == p.1)).flatMap Prod.snd = m.getD k [] := by
  rcases filter_beq_fst_eq_of_pairwise Std.HashMap.distinct_keys_toList k with h | ⟨p, hp, hkp, h⟩
  · rw [h, Std.HashMap.getD_eq_getD_getElem?]
    rcases hopt : m[k]? with _ | v
    · rfl
    · exfalso
      have hmem : (k, v) ∈ m.toList.filter (fun p => k == p.1) :=
        List.mem_filter.mpr ⟨Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hopt, BEq.refl k⟩
      rw [h] at hmem
      exact absurd hmem (List.not_mem_nil)
  · rw [h]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hpval : m[p.1]? = some p.2 := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hp
    rw [Std.HashMap.getD_eq_getD_getElem?, (Std.HashMap.getElem?_congr hkp).trans hpval]
    rfl

private theorem alter_insertSingletonOrAppend_equiv_insert
    (m : Std.HashMap ThreadLocation (List CommentRef)) (k : ThreadLocation) (v : CommentRef) :
    Std.HashMap.Equiv (m.alter k (insertSingletonOrAppend v)) (m.insert k (v :: m.getD k [])) := by
  apply Std.HashMap.Equiv.of_forall_getElem?_eq
  intro k'
  rw [Std.HashMap.getElem?_alter, Std.HashMap.getElem?_insert]
  split
  · next hk =>
    rw [Std.HashMap.getD_eq_getD_getElem?]
    rcases m[k]? with _ | vs <;> simp [insertSingletonOrAppend]
  · rfl

/-- `linkReplies`'s per-location accumulation (`alter` + `insertSingletonOrAppend`) prepends the
new ref to the flattened list of all roots, up to reordering. -/
private theorem flatMap_snd_toList_alter_insertSingletonOrAppend_perm
    (m : Std.HashMap ThreadLocation (List CommentRef)) (k : ThreadLocation) (v : CommentRef) :
    List.Perm ((m.alter k (insertSingletonOrAppend v)).toList.flatMap Prod.snd)
      (v :: m.toList.flatMap Prod.snd) := by
  have h1 := (Std.HashMap.Equiv.toList_perm (alter_insertSingletonOrAppend_equiv_insert m k v)).trans
    Std.HashMap.toList_insert_perm
  have h2 := h1.flatMap_right Prod.snd
  simp only [List.flatMap_cons, List.cons_append] at h2
  refine h2.trans (List.Perm.cons v ?_)
  have h3 := (List.filter_append_perm (fun p => k == p.1) m.toList).flatMap_right Prod.snd
  rw [List.flatMap_append, flatMap_snd_filter_beq_fst_toList_eq_getD] at h3
  have hpred : (fun x : ThreadLocation × List CommentRef => !(k == x.1)) =
      (fun x : ThreadLocation × List CommentRef => decide ¬(k == x.1) = true) := by
    funext x
    cases hb : k == x.1 <;> simp_all [beq_iff_eq]
  rwa [hpred] at h3

private theorem mem_alter_insertSingletonOrAppend
    (m : Std.HashMap ThreadLocation (List CommentRef)) (k k' : ThreadLocation) (v : CommentRef) :
    k' ∈ m.alter k (insertSingletonOrAppend v) ↔ k = k' ∨ k' ∈ m := by
  rw [Std.HashMap.mem_alter]
  split
  · next hk =>
    obtain rfl := beq_iff_eq.mp hk
    rcases m[k]? with _ | vs <;> simp [insertSingletonOrAppend]
  · next hk =>
    simp only [beq_iff_eq] at hk
    simp [hk]

private def registerServerCommentIds :
    (comments : List Comment) →
    (hCommentsHaveBackendIds : allCommentsHaveBackendId comments) →
    (s : CommentTreeBootstrapState) →
    CommentTreeBootstrapState
  | [], _, s => s
  | comment :: rest, hAll, s =>
    let treeNode : CommentThread := ⟨comment.ref, []⟩
    let serverId := comment.backendId.get (hAll comment List.mem_cons_self)
    registerServerCommentIds rest (fun c hc => hAll c (List.mem_cons_of_mem comment hc))
      { s with commentTreeNodes := s.commentTreeNodes.insert comment.ref treeNode,
               serverCommentIds := s.serverCommentIds.insert serverId comment.ref }

private theorem registerServerCommentIds_cons
    (head : Comment) (tail : List Comment) (hAll : allCommentsHaveBackendId (head :: tail))
    (s₀ : CommentTreeBootstrapState) :
    registerServerCommentIds (head :: tail) hAll s₀ =
      registerServerCommentIds tail (fun c hc => hAll c (List.mem_cons_of_mem head hc))
        { s₀ with commentTreeNodes := s₀.commentTreeNodes.insert head.ref ⟨head.ref, []⟩,
                  serverCommentIds := s₀.serverCommentIds.insert
                    (head.backendId.get (hAll head List.mem_cons_self)) head.ref } :=
  rfl

private theorem serverCommentIds_contains_of_contains
    (comments : List Comment) (hAll : allCommentsHaveBackendId comments)
    (s₀ : CommentTreeBootstrapState) (sid : ServerId) (h₀ : s₀.serverCommentIds.contains sid) :
    (registerServerCommentIds comments hAll s₀).serverCommentIds.contains sid := by
  induction comments generalizing s₀ with
  | nil => simpa [registerServerCommentIds] using h₀
  | cons head tail ih =>
    rw [registerServerCommentIds_cons]
    apply ih
    exact Std.HashMap.mem_insert.mpr (Or.inr h₀)


private theorem serverCommentIds_contains_of_mem
    (comments : List Comment) (hCommentsHaveBackendIds : allCommentsHaveBackendId comments)
    (s₀ : CommentTreeBootstrapState) (c : Comment) (hc : c ∈ comments) (sid : ServerId)
    (hsid : c.backendId = some sid) :
    (registerServerCommentIds comments hCommentsHaveBackendIds s₀).serverCommentIds.contains sid := by
  induction comments generalizing s₀ with
  | nil => cases hc
  | cons head tail ih =>
    rw [registerServerCommentIds_cons]
    rcases List.mem_cons.mp hc with rfl | hc'
    · apply serverCommentIds_contains_of_contains
      simp only [hsid, Option.get_some]
      exact Std.HashMap.mem_insert_self
    · exact ih _ _ hc'

/-- Whenever `serverCommentIds` maps a server id to a `CommentRef`, that ref is a live key of
`commentTreeNodes`: `registerServerCommentIds` always inserts into both maps in lockstep. Stated
via `[·]?` (rather than `.get` with a membership proof) so the induction is a plain rewrite,
with no dependent proof terms to carry across the `rw`. -/
private theorem commentTreeNodes_contains_of_serverCommentIds_getElem?
    (comments : List Comment) (hAll : allCommentsHaveBackendId comments)
    (s₀ : CommentTreeBootstrapState)
    (hInv : ∀ (sid : ServerId) (ref : CommentRef), s₀.serverCommentIds[sid]? = some ref → ref ∈ s₀.commentTreeNodes)
    (sid : ServerId) (ref : CommentRef)
    (hget : (registerServerCommentIds comments hAll s₀).serverCommentIds[sid]? = some ref) :
    ref ∈ (registerServerCommentIds comments hAll s₀).commentTreeNodes := by
  induction comments generalizing s₀ with
  | nil =>
    simp only [registerServerCommentIds] at hget
    exact hInv sid ref hget
  | cons head tail ih =>
    rw [registerServerCommentIds_cons] at hget ⊢
    refine ih _ _ ?_ hget
    intro sid' ref' hget'
    rw [Std.HashMap.getElem?_insert] at hget'
    split at hget'
    · exact Std.HashMap.mem_insert.mpr (Or.inl (by simp_all))
    · exact Std.HashMap.mem_insert.mpr (Or.inr (hInv sid' ref' hget'))

private theorem registerServerCommentIds_commentTreeNodes_contains_iff
    (comments : List Comment) (hAll : allCommentsHaveBackendId comments)
    (s₀ : CommentTreeBootstrapState) (ref : CommentRef) :
    (registerServerCommentIds comments hAll s₀).commentTreeNodes.contains ref ↔
      (∃ c, c ∈ comments ∧ c.ref = ref) ∨ s₀.commentTreeNodes.contains ref := by
  induction comments generalizing s₀ with
  | nil => simp [registerServerCommentIds]
  | cons head tail ih =>
    rw [registerServerCommentIds_cons]
    refine (ih _ _).trans ?_
    rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq]
    constructor
    · rintro (⟨c, hc, rfl⟩ | rfl | hs₀)
      · exact Or.inl ⟨c, List.mem_cons_of_mem head hc, rfl⟩
      · exact Or.inl ⟨head, List.mem_cons_self, rfl⟩
      · exact Or.inr hs₀
    · rintro (⟨c, hc, rfl⟩ | hs₀)
      · rcases List.mem_cons.mp hc with rfl | hc'
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl ⟨c, hc', rfl⟩
      · exact Or.inr (Or.inr hs₀)

private theorem registerServerCommentIds_locationRoots
    (comments : List Comment) (hAll : allCommentsHaveBackendId comments)
    (s₀ : CommentTreeBootstrapState) :
    (registerServerCommentIds comments hAll s₀).locationRoots = s₀.locationRoots := by
  induction comments generalizing s₀ with
  | nil => rfl
  | cons head tail ih =>
    rw [registerServerCommentIds_cons]
    exact (ih _ _).trans rfl

/-- Whatever `serverCommentIds` maps a server id to after `registerServerCommentIds` runs is either
inherited from the starting state, or is the ref of some comment in the batch with that backend id. -/
private theorem registerServerCommentIds_serverCommentIds_getElem?_mem
    (comments : List Comment) (hAll : allCommentsHaveBackendId comments) (s₀ : CommentTreeBootstrapState)
    (sid : ServerId) (ref : CommentRef)
    (hget : (registerServerCommentIds comments hAll s₀).serverCommentIds[sid]? = some ref) :
    s₀.serverCommentIds[sid]? = some ref ∨ ∃ c, c ∈ comments ∧ c.backendId = some sid ∧ c.ref = ref := by
  induction comments generalizing s₀ with
  | nil => simpa [registerServerCommentIds] using hget
  | cons head tail ih =>
    rw [registerServerCommentIds_cons] at hget
    rcases ih _ _ hget with h | ⟨c, hc, hcbackend, hcref⟩
    · rw [Std.HashMap.getElem?_insert] at h
      split at h
      · next hcond =>
        right
        refine ⟨head, List.mem_cons_self, ?_, Option.some.inj h⟩
        rw [← beq_iff_eq.mp hcond]
        exact Option.some_get (hAll head List.mem_cons_self) |>.symm
      · left; exact h
    · right; exact ⟨c, List.mem_cons_of_mem head hc, hcbackend, hcref⟩

private theorem registerServerCommentIds_rootMatchesKey
    (comments : List Comment) (hAll : allCommentsHaveBackendId comments)
    (s₀ : CommentTreeBootstrapState)
    (hInv : ∀ (ref : CommentRef) (val : CommentThread), s₀.commentTreeNodes[ref]? = some val → val.value = ref) :
    ∀ (ref : CommentRef) (val : CommentThread),
      (registerServerCommentIds comments hAll s₀).commentTreeNodes[ref]? = some val → val.value = ref := by
  induction comments generalizing s₀ with
  | nil => simpa [registerServerCommentIds] using hInv
  | cons head tail ih =>
    rw [registerServerCommentIds_cons]
    apply ih
    intro ref val hget
    rw [Std.HashMap.getElem?_insert] at hget
    split at hget
    · rename_i h
      rw [← Option.some.inj hget]
      exact beq_iff_eq.mp h
    · exact hInv ref val hget

/-- Every node `registerServerCommentIds` inserts starts out childless (`⟨comment.ref, []⟩`), and it
never modifies an existing entry, so every live node still has no children once it's done. This is
half of what's needed to know that `linkReplies` (which is the only step that ever adds children) is
the sole source of any child ref, and so every child ref is itself a registered comment. -/
private theorem registerServerCommentIds_children_empty
    (comments : List Comment) (hAll : allCommentsHaveBackendId comments)
    (s₀ : CommentTreeBootstrapState)
    (hInv : ∀ (ref : CommentRef) (val : CommentThread), s₀.commentTreeNodes[ref]? = some val → val.children = []) :
    ∀ (ref : CommentRef) (val : CommentThread),
      (registerServerCommentIds comments hAll s₀).commentTreeNodes[ref]? = some val → val.children = [] := by
  induction comments generalizing s₀ with
  | nil => simpa [registerServerCommentIds] using hInv
  | cons head tail ih =>
    rw [registerServerCommentIds_cons]
    apply ih
    intro ref val hget
    rw [Std.HashMap.getElem?_insert] at hget
    split at hget
    · rw [← Option.some.inj hget]
    · exact hInv ref val hget

/-- Attach every reply comment to its parent's tree node, and collect the root comments into
`locationRoots`. -/
private def linkReplies (serverCommentIds : Std.HashMap ServerId CommentRef) :
    (comments : List Comment) →
    (hParentsHaveNode : ∀ c, c ∈ comments → ∀ parentId, c.parent = some parentId → parentId ∈ serverCommentIds) →
    (s : CommentTreeBootstrapState) →
    (hInv : ∀ sid (h : sid ∈ serverCommentIds), serverCommentIds.get sid h ∈ s.commentTreeNodes) →
    CommentTreeBootstrapState
  | [], _, s, _ => s
  | comment :: rest, hParentsHaveNode, s, hInv =>
    match h2 : comment.parent with
    | none =>
      let s' := { s with locationRoots :=
        s.locationRoots.alter comment.location.asThreadLocation (insertSingletonOrAppend comment.ref) }
      linkReplies serverCommentIds rest (fun c hc => hParentsHaveNode c (List.mem_cons_of_mem comment hc)) s' hInv
    | some parentId =>
      have hContains : parentId ∈ serverCommentIds := hParentsHaveNode comment List.mem_cons_self parentId h2
      let parentNodeRef := serverCommentIds.get parentId hContains
      have hParentNodeRefMem : parentNodeRef ∈ s.commentTreeNodes := hInv parentId hContains
      let parentTreeNode := s.commentTreeNodes.get parentNodeRef hParentNodeRefMem
      let s' : CommentTreeBootstrapState :=
        { s with commentTreeNodes := s.commentTreeNodes.insert parentNodeRef (parentTreeNode.addChild comment.ref) }
      have hInv' : ∀ sid (h : sid ∈ serverCommentIds), serverCommentIds.get sid h ∈ s'.commentTreeNodes :=
        fun sid h => Std.HashMap.mem_insert.mpr (Or.inr (hInv sid h))
      linkReplies serverCommentIds rest (fun c hc => hParentsHaveNode c (List.mem_cons_of_mem comment hc)) s' hInv'

private theorem linkReplies_nil
    (serverCommentIds : Std.HashMap ServerId CommentRef)
    (hParentsHaveNode : ∀ c, c ∈ ([] : List Comment) → ∀ parentId, c.parent = some parentId → parentId ∈ serverCommentIds)
    (s : CommentTreeBootstrapState)
    (hInv : ∀ sid (h : sid ∈ serverCommentIds), serverCommentIds.get sid h ∈ s.commentTreeNodes) :
    linkReplies serverCommentIds [] hParentsHaveNode s hInv = s :=
  rfl

private theorem linkReplies_cons_none
    (serverCommentIds : Std.HashMap ServerId CommentRef)
    (comment : Comment) (rest : List Comment) (h2 : comment.parent = none)
    (hParentsHaveNode : ∀ c, c ∈ comment :: rest → ∀ parentId, c.parent = some parentId → parentId ∈ serverCommentIds)
    (s : CommentTreeBootstrapState)
    (hInv : ∀ sid (h : sid ∈ serverCommentIds), serverCommentIds.get sid h ∈ s.commentTreeNodes) :
    linkReplies serverCommentIds (comment :: rest) hParentsHaveNode s hInv =
      linkReplies serverCommentIds rest (fun c hc => hParentsHaveNode c (List.mem_cons_of_mem comment hc))
        { s with locationRoots :=
            s.locationRoots.alter comment.location.asThreadLocation (insertSingletonOrAppend comment.ref) }
        hInv := by
  simp only [linkReplies]
  split
  · rfl
  · simp_all

private theorem linkReplies_cons_some
    (serverCommentIds : Std.HashMap ServerId CommentRef)
    (comment : Comment) (rest : List Comment) (parentId : ServerId) (h2 : comment.parent = some parentId)
    (hParentsHaveNode : ∀ c, c ∈ comment :: rest → ∀ parentId, c.parent = some parentId → parentId ∈ serverCommentIds)
    (s : CommentTreeBootstrapState)
    (hInv : ∀ sid (h : sid ∈ serverCommentIds), serverCommentIds.get sid h ∈ s.commentTreeNodes)
    (hContains : parentId ∈ serverCommentIds) :
    linkReplies serverCommentIds (comment :: rest) hParentsHaveNode s hInv =
      linkReplies serverCommentIds rest (fun c hc => hParentsHaveNode c (List.mem_cons_of_mem comment hc))
        (let parentNodeRef := serverCommentIds.get parentId hContains
         let parentTreeNode := s.commentTreeNodes.get parentNodeRef (hInv parentId hContains)
         { s with commentTreeNodes := s.commentTreeNodes.insert parentNodeRef (parentTreeNode.addChild comment.ref) })
        (fun sid h => Std.HashMap.mem_insert.mpr (Or.inr (hInv sid h))) := by
  simp only [linkReplies]
  split
  · simp_all
  · next parentId' heq =>
    obtain rfl : parentId' = parentId := Option.some.inj (heq.symm.trans h2)
    rfl

/-- Membership in `linkReplies`'s final `locationRoots` bucket at `loc` is inherited from the
starting state `s`, or comes from some root comment (`parent = none`) at that location. -/
private theorem linkReplies_locationRoots_getD_iff (serverCommentIds : Std.HashMap ServerId CommentRef) :
    (comments : List Comment) →
    (hParentsHaveNode : ∀ c, c ∈ comments → ∀ parentId, c.parent = some parentId → parentId ∈ serverCommentIds) →
    (s : CommentTreeBootstrapState) →
    (hInv : ∀ sid (h : sid ∈ serverCommentIds), serverCommentIds.get sid h ∈ s.commentTreeNodes) →
    (loc : ThreadLocation) → (ref : CommentRef) →
    ref ∈ (linkReplies serverCommentIds comments hParentsHaveNode s hInv).locationRoots.getD loc [] ↔
      ref ∈ s.locationRoots.getD loc [] ∨
        ∃ c, c ∈ comments ∧ c.parent = none ∧ c.ref = ref ∧ c.location.asThreadLocation = loc
  | [], _, s, _, _, _ => by rw [linkReplies_nil]; simp
  | comment :: rest, hParentsHaveNode, s, hInv, loc, ref => by
    rcases h2 : comment.parent with _ | parentId
    · rw [linkReplies_cons_none serverCommentIds comment rest h2 hParentsHaveNode s hInv,
        linkReplies_locationRoots_getD_iff serverCommentIds rest _ _ _ loc ref,
        mem_getD_alter_insertSingletonOrAppend]
      constructor
      · rintro ((⟨hkloc, hvref⟩ | h) | h)
        · exact Or.inr ⟨comment, List.mem_cons_self, h2, hvref.symm, hkloc⟩
        · exact Or.inl h
        · obtain ⟨c, hc, hnone, hcref, hcloc⟩ := h
          exact Or.inr ⟨c, List.mem_cons_of_mem comment hc, hnone, hcref, hcloc⟩
      · rintro (h | ⟨c, hc, hnone, hcref, hcloc⟩)
        · exact Or.inl (Or.inr h)
        · rcases List.mem_cons.mp hc with rfl | hc'
          · exact Or.inl (Or.inl ⟨hcloc, hcref.symm⟩)
          · exact Or.inr ⟨c, hc', hnone, hcref, hcloc⟩
    · have hContains : parentId ∈ serverCommentIds := hParentsHaveNode comment List.mem_cons_self parentId h2
      rw [linkReplies_cons_some serverCommentIds comment rest parentId h2 hParentsHaveNode s hInv hContains,
        linkReplies_locationRoots_getD_iff serverCommentIds rest _ _ _ loc ref]
      constructor
      · rintro (h | ⟨c, hc, hnone, hcref, hcloc⟩)
        · exact Or.inl h
        · exact Or.inr ⟨c, List.mem_cons_of_mem comment hc, hnone, hcref, hcloc⟩
      · rintro (h | ⟨c, hc, hnone, hcref, hcloc⟩)
        · exact Or.inl h
        · rcases List.mem_cons.mp hc with rfl | hc'
          · simp [h2] at hnone
          · exact Or.inr ⟨c, hc', hnone, hcref, hcloc⟩

/-- Every `locationRoots` key of `linkReplies`'s result is either already a key of `s`, or the
location of some root comment (`parent = none`) in the batch. -/
private theorem linkReplies_locationRoots_mem_of_mem (serverCommentIds : Std.HashMap ServerId CommentRef) :
    (comments : List Comment) →
    (hParentsHaveNode : ∀ c, c ∈ comments → ∀ parentId, c.parent = some parentId → parentId ∈ serverCommentIds) →
    (s : CommentTreeBootstrapState) →
    (hInv : ∀ sid (h : sid ∈ serverCommentIds), serverCommentIds.get sid h ∈ s.commentTreeNodes) →
    (loc : ThreadLocation) →
    loc ∈ (linkReplies serverCommentIds comments hParentsHaveNode s hInv).locationRoots →
      loc ∈ s.locationRoots ∨ ∃ c, c ∈ comments ∧ c.parent = none ∧ c.location.asThreadLocation = loc
  | [], _, s, _, _ => by rw [linkReplies_nil]; exact Or.inl
  | comment :: rest, hParentsHaveNode, s, hInv, loc => by
    rcases h2 : comment.parent with _ | parentId
    · rw [linkReplies_cons_none serverCommentIds comment rest h2 hParentsHaveNode s hInv]
      intro h
      rcases linkReplies_locationRoots_mem_of_mem serverCommentIds rest _ _ _ loc h with h | ⟨c, hc, hnone, hcloc⟩
      · rcases (mem_alter_insertSingletonOrAppend s.locationRoots comment.location.asThreadLocation loc
          comment.ref).mp h with hkloc | h'
        · exact Or.inr ⟨comment, List.mem_cons_self, h2, hkloc⟩
        · exact Or.inl h'
      · exact Or.inr ⟨c, List.mem_cons_of_mem comment hc, hnone, hcloc⟩
    · have hContains : parentId ∈ serverCommentIds := hParentsHaveNode comment List.mem_cons_self parentId h2
      rw [linkReplies_cons_some serverCommentIds comment rest parentId h2 hParentsHaveNode s hInv hContains]
      intro h
      rcases linkReplies_locationRoots_mem_of_mem serverCommentIds rest _ _ _ loc h with h | ⟨c, hc, hnone, hcloc⟩
      · exact Or.inl h
      · exact Or.inr ⟨c, List.mem_cons_of_mem comment hc, hnone, hcloc⟩

/-- If the starting `locationRoots` (flattened across all locations) is already `Nodup` and
disjoint from the refs of comments not yet processed, `linkReplies` preserves `Nodup`: every root
comment's ref is fresh (by `hDisjoint`) when it gets pushed. -/
private theorem linkReplies_locationRoots_nodup (serverCommentIds : Std.HashMap ServerId CommentRef) :
    (comments : List Comment) →
    (hParentsHaveNode : ∀ c, c ∈ comments → ∀ parentId, c.parent = some parentId → parentId ∈ serverCommentIds) →
    (s : CommentTreeBootstrapState) →
    (hInv : ∀ sid (h : sid ∈ serverCommentIds), serverCommentIds.get sid h ∈ s.commentTreeNodes) →
    (hCommentsNodup : (comments.map Comment.ref).Nodup) →
    (hSNodup : (s.locationRoots.toList.flatMap Prod.snd).Nodup) →
    (hDisjoint : ∀ ref, ref ∈ s.locationRoots.toList.flatMap Prod.snd → ref ∉ comments.map Comment.ref) →
    ((linkReplies serverCommentIds comments hParentsHaveNode s hInv).locationRoots.toList.flatMap Prod.snd).Nodup
  | [], _, s, _, _, hSNodup, _ => by rw [linkReplies_nil]; exact hSNodup
  | comment :: rest, hParentsHaveNode, s, hInv, hCommentsNodup, hSNodup, hDisjoint => by
    rcases h2 : comment.parent with _ | parentId
    · rw [linkReplies_cons_none serverCommentIds comment rest h2 hParentsHaveNode s hInv]
      have hperm := flatMap_snd_toList_alter_insertSingletonOrAppend_perm s.locationRoots
        comment.location.asThreadLocation comment.ref
      apply linkReplies_locationRoots_nodup
      · exact (List.nodup_cons.mp hCommentsNodup).2
      · rw [hperm.nodup_iff]
        refine List.nodup_cons.mpr ⟨fun hmem => hDisjoint comment.ref hmem ?_, hSNodup⟩
        simp
      · intro ref href
        rw [hperm.mem_iff, List.mem_cons] at href
        rcases href with rfl | href
        · exact (List.nodup_cons.mp hCommentsNodup).1
        · exact fun hcontra => hDisjoint ref href (List.mem_cons_of_mem comment.ref hcontra)
    · have hContains : parentId ∈ serverCommentIds := hParentsHaveNode comment List.mem_cons_self parentId h2
      rw [linkReplies_cons_some serverCommentIds comment rest parentId h2 hParentsHaveNode s hInv hContains]
      apply linkReplies_locationRoots_nodup
      · exact (List.nodup_cons.mp hCommentsNodup).2
      · exact hSNodup
      · exact fun ref href hcontra => hDisjoint ref href (List.mem_cons_of_mem comment.ref hcontra)

/-- Once `childRef` is a child of the node at `nodeRef`, it stays a child through the rest of
`linkReplies`'s processing: further updates at `nodeRef` only ever prepend more children (via
`Tree.addChild`), and updates at any other key don't touch `nodeRef`'s entry at all. -/
private theorem linkReplies_children_mem_preserved (serverCommentIds : Std.HashMap ServerId CommentRef) :
    (comments : List Comment) →
    (hParentsHaveNode : ∀ c, c ∈ comments → ∀ parentId, c.parent = some parentId → parentId ∈ serverCommentIds) →
    (s : CommentTreeBootstrapState) →
    (hInv : ∀ sid (h : sid ∈ serverCommentIds), serverCommentIds.get sid h ∈ s.commentTreeNodes) →
    (nodeRef childRef : CommentRef) → (node : CommentThread) →
    s.commentTreeNodes[nodeRef]? = some node → childRef ∈ node.children →
    ∃ node', (linkReplies serverCommentIds comments hParentsHaveNode s hInv).commentTreeNodes[nodeRef]? = some node' ∧
      childRef ∈ node'.children
  | [], _, s, _, _, _, node, hget, hchild => by rw [linkReplies_nil]; exact ⟨node, hget, hchild⟩
  | comment :: rest, hParentsHaveNode, s, hInv, nodeRef, childRef, node, hget, hchild => by
    rcases h2 : comment.parent with _ | parentId
    · rw [linkReplies_cons_none serverCommentIds comment rest h2 hParentsHaveNode s hInv]
      exact linkReplies_children_mem_preserved serverCommentIds rest _ _ _ nodeRef childRef node hget hchild
    · have hContains : parentId ∈ serverCommentIds := hParentsHaveNode comment List.mem_cons_self parentId h2
      rw [linkReplies_cons_some serverCommentIds comment rest parentId h2 hParentsHaveNode s hInv hContains]
      by_cases hkey : serverCommentIds.get parentId hContains = nodeRef
      · subst hkey
        have heq : s.commentTreeNodes.get (serverCommentIds.get parentId hContains) (hInv parentId hContains) =
            node :=
          Option.some.inj (((Std.HashMap.getElem?_eq_some_getElem (hInv parentId hContains)).symm).trans hget)
        refine linkReplies_children_mem_preserved serverCommentIds rest _ _ _
          (serverCommentIds.get parentId hContains) childRef (Tree.addChild node comment.ref) ?_
          (List.mem_cons_of_mem _ hchild)
        rw [Std.HashMap.getElem?_insert, if_pos (BEq.refl _), heq]
      · refine linkReplies_children_mem_preserved serverCommentIds rest _ _ _ nodeRef childRef node ?_ hchild
        rw [Std.HashMap.getElem?_insert, if_neg (fun h => hkey (beq_iff_eq.mp h))]
        exact hget

/-- Every reply comment's ref becomes (and, by the previous lemma, stays) a child of its resolved
parent's node once `linkReplies` processes it. -/
private theorem linkReplies_children_mem_of_parent (serverCommentIds : Std.HashMap ServerId CommentRef) :
    (comments : List Comment) →
    (hParentsHaveNode : ∀ c, c ∈ comments → ∀ parentId, c.parent = some parentId → parentId ∈ serverCommentIds) →
    (s : CommentTreeBootstrapState) →
    (hInv : ∀ sid (h : sid ∈ serverCommentIds), serverCommentIds.get sid h ∈ s.commentTreeNodes) →
    (comment : Comment) → comment ∈ comments → (parentId : ServerId) → comment.parent = some parentId →
    (hContains : parentId ∈ serverCommentIds) →
    ∃ node', (linkReplies serverCommentIds comments hParentsHaveNode s hInv).commentTreeNodes[
        serverCommentIds.get parentId hContains]? = some node' ∧ comment.ref ∈ node'.children
  | [], _, _, _, comment, hc, _, _, _ => absurd hc List.not_mem_nil
  | head :: rest, hParentsHaveNode, s, hInv, comment, hc, parentId, hparent, hContains => by
    rcases List.mem_cons.mp hc with rfl | hc'
    · rcases h2 : comment.parent with _ | parentId'
      · rw [h2] at hparent; exact absurd hparent (by simp)
      · have hpid : parentId' = parentId := Option.some.inj (h2 ▸ hparent)
        subst parentId'
        rw [linkReplies_cons_some serverCommentIds comment rest parentId h2 hParentsHaveNode s hInv hContains]
        refine linkReplies_children_mem_preserved serverCommentIds rest _ _ _
          (serverCommentIds.get parentId hContains) comment.ref
          (Tree.addChild (s.commentTreeNodes.get (serverCommentIds.get parentId hContains)
            (hInv parentId hContains)) comment.ref) ?_ List.mem_cons_self
        rw [Std.HashMap.getElem?_insert, if_pos (BEq.refl _)]
    · rcases h2 : head.parent with _ | parentId'
      · rw [linkReplies_cons_none serverCommentIds head rest h2 hParentsHaveNode s hInv]
        exact linkReplies_children_mem_of_parent serverCommentIds rest _ _ _ comment hc' parentId hparent hContains
      · have hContains' : parentId' ∈ serverCommentIds := hParentsHaveNode head List.mem_cons_self parentId' h2
        rw [linkReplies_cons_some serverCommentIds head rest parentId' h2 hParentsHaveNode s hInv hContains']
        exact linkReplies_children_mem_of_parent serverCommentIds rest _ _ _ comment hc' parentId hparent hContains

/-- If every child ref appearing in `s`'s nodes is itself a registered comment ref, that property
survives `linkReplies`: the only new child `linkReplies` ever inserts (via `Tree.addChild`) is
`comment.ref` for the `comment` being processed, which `hCommentsRegistered` shows is already
registered in `s`, and `s`'s existing keys are never removed. -/
private theorem linkReplies_children_subset (serverCommentIds : Std.HashMap ServerId CommentRef) :
    (comments : List Comment) →
    (hParentsHaveNode : ∀ c, c ∈ comments → ∀ parentId, c.parent = some parentId → parentId ∈ serverCommentIds) →
    (s : CommentTreeBootstrapState) →
    (hInv : ∀ sid (h : sid ∈ serverCommentIds), serverCommentIds.get sid h ∈ s.commentTreeNodes) →
    (hCommentsRegistered : ∀ c, c ∈ comments → c.ref ∈ s.commentTreeNodes) →
    (hSChildrenSubset : ∀ (ref : CommentRef) (node : CommentThread), s.commentTreeNodes[ref]? = some node →
      ∀ child, child ∈ node.children → child ∈ s.commentTreeNodes) →
    ∀ (ref : CommentRef) (node : CommentThread),
      (linkReplies serverCommentIds comments hParentsHaveNode s hInv).commentTreeNodes[ref]? = some node →
      ∀ child, child ∈ node.children → child ∈ (linkReplies serverCommentIds comments hParentsHaveNode s hInv).commentTreeNodes
  | [], _, s, _, _, hSChildrenSubset => by rw [linkReplies_nil]; exact hSChildrenSubset
  | comment :: rest, hParentsHaveNode, s, hInv, hCommentsRegistered, hSChildrenSubset => by
    rcases h2 : comment.parent with _ | parentId
    · rw [linkReplies_cons_none serverCommentIds comment rest h2 hParentsHaveNode s hInv]
      apply linkReplies_children_subset
      · exact fun c hc => hCommentsRegistered c (List.mem_cons_of_mem comment hc)
      · exact hSChildrenSubset
    · have hContains : parentId ∈ serverCommentIds := hParentsHaveNode comment List.mem_cons_self parentId h2
      rw [linkReplies_cons_some serverCommentIds comment rest parentId h2 hParentsHaveNode s hInv hContains]
      apply linkReplies_children_subset
      · exact fun c hc => Std.HashMap.mem_insert.mpr (Or.inr (hCommentsRegistered c (List.mem_cons_of_mem comment hc)))
      · intro ref node hget child hchild
        rw [Std.HashMap.getElem?_insert] at hget
        split at hget
        · next hkeq =>
          have hnode : node = Tree.addChild (s.commentTreeNodes.get (serverCommentIds.get parentId hContains)
              (hInv parentId hContains)) comment.ref := (Option.some.inj hget).symm
          rw [hnode] at hchild
          rcases List.mem_cons.mp hchild with rfl | hchild
          · exact Std.HashMap.mem_insert.mpr (Or.inr (hCommentsRegistered comment List.mem_cons_self))
          · exact Std.HashMap.mem_insert.mpr (Or.inr
              (hSChildrenSubset _ _ (Std.HashMap.getElem?_eq_some_getElem (hInv parentId hContains)) child hchild))
        · next hkne =>
          exact Std.HashMap.mem_insert.mpr (Or.inr (hSChildrenSubset ref node hget child hchild))

/-- `linkReplies` never adds or removes `commentTreeNodes` keys: it only ever updates the value at
an already-live key (the resolved parent), via `hInv`. -/
private theorem linkReplies_commentTreeNodes_contains_iff (serverCommentIds : Std.HashMap ServerId CommentRef) :
    (comments : List Comment) →
    (hParentsHaveNode : ∀ c, c ∈ comments → ∀ parentId, c.parent = some parentId → parentId ∈ serverCommentIds) →
    (s : CommentTreeBootstrapState) →
    (hInv : ∀ sid (h : sid ∈ serverCommentIds), serverCommentIds.get sid h ∈ s.commentTreeNodes) →
    (ref : CommentRef) →
    (linkReplies serverCommentIds comments hParentsHaveNode s hInv).commentTreeNodes.contains ref ↔
      s.commentTreeNodes.contains ref
  | [], _, s, _, _ => by rw [linkReplies_nil]
  | comment :: rest, hParentsHaveNode, s, hInv, ref => by
    rcases h2 : comment.parent with _ | parentId
    · rw [linkReplies_cons_none serverCommentIds comment rest h2 hParentsHaveNode s hInv]
      exact linkReplies_commentTreeNodes_contains_iff serverCommentIds rest _ _ _ ref
    · have hContains : parentId ∈ serverCommentIds := hParentsHaveNode comment List.mem_cons_self parentId h2
      rw [linkReplies_cons_some serverCommentIds comment rest parentId h2 hParentsHaveNode s hInv hContains]
      refine (linkReplies_commentTreeNodes_contains_iff serverCommentIds rest _ _ _ ref).trans ?_
      rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq]
      constructor
      · rintro (rfl | h)
        · exact Std.HashMap.mem_iff_contains.mp (hInv parentId hContains)
        · exact h
      · exact Or.inr

/-- `Tree.addChild` never changes `.value`, so `linkReplies` preserves the "each node's `.value`
matches its own key" invariant. -/
private theorem linkReplies_rootMatchesKey (serverCommentIds : Std.HashMap ServerId CommentRef) :
    (comments : List Comment) →
    (hParentsHaveNode : ∀ c, c ∈ comments → ∀ parentId, c.parent = some parentId → parentId ∈ serverCommentIds) →
    (s : CommentTreeBootstrapState) →
    (hInv : ∀ sid (h : sid ∈ serverCommentIds), serverCommentIds.get sid h ∈ s.commentTreeNodes) →
    (hRootMatch : ∀ (ref : CommentRef) (val : CommentThread), s.commentTreeNodes[ref]? = some val → val.value = ref) →
    ∀ (ref : CommentRef) (val : CommentThread),
      (linkReplies serverCommentIds comments hParentsHaveNode s hInv).commentTreeNodes[ref]? = some val →
        val.value = ref
  | [], _, s, _, hRootMatch => by rw [linkReplies_nil]; exact hRootMatch
  | comment :: rest, hParentsHaveNode, s, hInv, hRootMatch => by
    rcases h2 : comment.parent with _ | parentId
    · rw [linkReplies_cons_none serverCommentIds comment rest h2 hParentsHaveNode s hInv]
      exact linkReplies_rootMatchesKey serverCommentIds rest _ _ _ hRootMatch
    · have hContains : parentId ∈ serverCommentIds := hParentsHaveNode comment List.mem_cons_self parentId h2
      rw [linkReplies_cons_some serverCommentIds comment rest parentId h2 hParentsHaveNode s hInv hContains]
      refine linkReplies_rootMatchesKey serverCommentIds rest _ _ _ ?_
      intro ref val hget
      rw [Std.HashMap.getElem?_insert] at hget
      split at hget
      · rename_i h
        have hpeq : serverCommentIds.get parentId hContains = ref := beq_iff_eq.mp h
        have hval : (s.commentTreeNodes.get (serverCommentIds.get parentId hContains)
            (hInv parentId hContains)).value = serverCommentIds.get parentId hContains :=
          hRootMatch _ _ (Std.HashMap.getElem?_eq_some_getElem (hInv parentId hContains))
        rw [← Option.some.inj hget]
        simpa [Tree.addChild, hpeq] using hval.trans hpeq
      · exact hRootMatch ref val hget

/-- Every parent id referenced by a comment in the batch ends up in `serverCommentIds` after
`registerServerCommentIds` runs, regardless of the starting state `s₀`: `hParentsInComments`
locates the parent's own comment in the batch, and `registerServerCommentIds` registers every
comment in the batch. -/
private theorem bootstrapParentsHaveNode
    (comments : List Comment) (hCommentsHaveBackendIds : allCommentsHaveBackendId comments)
    (hParentsInComments : allParentsInComments comments) (s₀ : CommentTreeBootstrapState) :
    ∀ c, c ∈ comments → ∀ parentId, c.parent = some parentId →
      parentId ∈ (registerServerCommentIds comments hCommentsHaveBackendIds s₀).serverCommentIds := by
  intro c hc parentId hp
  obtain ⟨c', hc', hbackend⟩ := hParentsInComments c hc parentId hp
  exact Std.HashMap.mem_iff_contains.mpr
    (serverCommentIds_contains_of_mem comments hCommentsHaveBackendIds s₀ c' hc' parentId hbackend)

/-- The `commentTreeNodes`/`serverCommentIds` invariant required by `linkReplies` survives
`registerServerCommentIds`, provided it already held of the starting state `s₀`. -/
private theorem bootstrapCommentTreeNodesInv
    (comments : List Comment) (hCommentsHaveBackendIds : allCommentsHaveBackendId comments)
    (s₀ : CommentTreeBootstrapState)
    (hInv : ∀ sid (h : sid ∈ s₀.serverCommentIds), s₀.serverCommentIds.get sid h ∈ s₀.commentTreeNodes) :
    ∀ sid (h : sid ∈ (registerServerCommentIds comments hCommentsHaveBackendIds s₀).serverCommentIds),
      (registerServerCommentIds comments hCommentsHaveBackendIds s₀).serverCommentIds.get sid h ∈
        (registerServerCommentIds comments hCommentsHaveBackendIds s₀).commentTreeNodes := by
  intro sid h
  apply commentTreeNodes_contains_of_serverCommentIds_getElem? comments hCommentsHaveBackendIds s₀
  · intro sid' ref' hget'
    have hmem : sid' ∈ s₀.serverCommentIds := Std.HashMap.mem_iff_isSome_getElem?.mpr (by simp [hget'])
    have := hInv sid' hmem
    rwa [Std.HashMap.get_eq_getElem, show s₀.serverCommentIds[sid']'hmem = ref' by
      have h' := Std.HashMap.getElem?_eq_some_getElem (m := s₀.serverCommentIds) hmem
      rw [hget'] at h'
      exact Option.some.inj h'.symm] at this
  · exact Std.HashMap.getElem?_eq_some_getElem
      (m := (registerServerCommentIds comments hCommentsHaveBackendIds s₀).serverCommentIds) h |>.trans
        (by rw [Std.HashMap.get_eq_getElem])

private def bootstrapCommentTrees (comments : List Comment)
                                  (hCommentsHaveBackendIds : allCommentsHaveBackendId comments)
                                  (hParentsInComments : allParentsInComments comments)
                                  (s₀ : CommentTreeBootstrapState)
                                  (hInv : ∀ sid (h : sid ∈ s₀.serverCommentIds),
                                    s₀.serverCommentIds.get sid h ∈ s₀.commentTreeNodes)
                                  : CommentTreeBootstrapState :=
  let s₁ := registerServerCommentIds comments hCommentsHaveBackendIds s₀
  linkReplies s₁.serverCommentIds comments
    (bootstrapParentsHaveNode comments hCommentsHaveBackendIds hParentsInComments s₀)
    s₁
    (bootstrapCommentTreeNodesInv comments hCommentsHaveBackendIds s₀ hInv)

private theorem bootstrapCommentTrees_locationRoots_getD_iff
    (comments : List Comment) (hCommentsHaveBackendIds : allCommentsHaveBackendId comments)
    (hParentsInComments : allParentsInComments comments) (loc : ThreadLocation) (ref : CommentRef) :
    ref ∈ (bootstrapCommentTrees comments hCommentsHaveBackendIds hParentsInComments
        emptyBootstrapState (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)).locationRoots.getD loc [] ↔
      ∃ c, c ∈ comments ∧ c.parent = none ∧ c.ref = ref ∧ c.location.asThreadLocation = loc := by
  unfold bootstrapCommentTrees
  rw [linkReplies_locationRoots_getD_iff, registerServerCommentIds_locationRoots]
  simp [emptyBootstrapState]

private theorem bootstrapCommentTrees_locationRoots_mem_of_mem
    (comments : List Comment) (hCommentsHaveBackendIds : allCommentsHaveBackendId comments)
    (hParentsInComments : allParentsInComments comments) (loc : ThreadLocation) :
    loc ∈ (bootstrapCommentTrees comments hCommentsHaveBackendIds hParentsInComments
        emptyBootstrapState (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)).locationRoots →
      ∃ c, c ∈ comments ∧ c.parent = none ∧ c.location.asThreadLocation = loc := by
  unfold bootstrapCommentTrees
  intro h
  rcases linkReplies_locationRoots_mem_of_mem _ _ _ _ _ loc h with h' | h'
  · rw [registerServerCommentIds_locationRoots] at h'
    simp [emptyBootstrapState] at h'
  · exact h'

private theorem bootstrapCommentTrees_locationRootsNodup
    (comments : List Comment) (hCommentsHaveBackendIds : allCommentsHaveBackendId comments)
    (hParentsInComments : allParentsInComments comments) (hRefsNodup : commentRefsNodup comments) :
    ((bootstrapCommentTrees comments hCommentsHaveBackendIds hParentsInComments
        emptyBootstrapState (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)).locationRoots.toList.flatMap
        Prod.snd).Nodup := by
  unfold bootstrapCommentTrees
  apply linkReplies_locationRoots_nodup
  · exact hRefsNodup
  · rw [registerServerCommentIds_locationRoots]
    simp [emptyBootstrapState]
  · intro ref href
    rw [registerServerCommentIds_locationRoots] at href
    simp [emptyBootstrapState] at href

private theorem bootstrapCommentTrees_children_mem_of_parent
    (comments : List Comment) (hCommentsHaveBackendIds : allCommentsHaveBackendId comments)
    (hParentsInComments : allParentsInComments comments)
    (comment : Comment) (hc : comment ∈ comments) (parentId : ServerId) (hparent : comment.parent = some parentId)
    (hContains : parentId ∈
      (registerServerCommentIds comments hCommentsHaveBackendIds emptyBootstrapState).serverCommentIds) :
    ∃ node', (bootstrapCommentTrees comments hCommentsHaveBackendIds hParentsInComments
        emptyBootstrapState (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)).commentTreeNodes[
      (registerServerCommentIds comments hCommentsHaveBackendIds emptyBootstrapState).serverCommentIds.get parentId
        hContains]? = some node' ∧ comment.ref ∈ node'.children := by
  unfold bootstrapCommentTrees
  exact linkReplies_children_mem_of_parent _ comments _ _ _ comment hc parentId hparent hContains

private theorem bootstrapCommentTrees_commentTreeNodes_contains_iff
    (comments : List Comment) (hCommentsHaveBackendIds : allCommentsHaveBackendId comments)
    (hParentsInComments : allParentsInComments comments) (ref : CommentRef) :
    (bootstrapCommentTrees comments hCommentsHaveBackendIds hParentsInComments
        emptyBootstrapState (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)).commentTreeNodes.contains
        ref ↔
      ∃ c, c ∈ comments ∧ c.ref = ref := by
  unfold bootstrapCommentTrees
  rw [linkReplies_commentTreeNodes_contains_iff, registerServerCommentIds_commentTreeNodes_contains_iff]
  simp [emptyBootstrapState]

/-- Every child ref appearing in any live node is itself a registered comment ref: the only source
of children is `linkReplies` attaching `comment.ref` for comments already registered by
`registerServerCommentIds` (`linkReplies_children_subset`), starting from the fact that freshly
registered nodes have no children yet (`registerServerCommentIds_children_empty`). -/
private theorem bootstrapCommentTrees_children_registered
    (comments : List Comment) (hCommentsHaveBackendIds : allCommentsHaveBackendId comments)
    (hParentsInComments : allParentsInComments comments) (ref : CommentRef) (node : CommentThread)
    (hget : (bootstrapCommentTrees comments hCommentsHaveBackendIds hParentsInComments
        emptyBootstrapState (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)).commentTreeNodes[ref]? =
      some node)
    (child : CommentRef) (hchild : child ∈ node.children) :
    (bootstrapCommentTrees comments hCommentsHaveBackendIds hParentsInComments
        emptyBootstrapState (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)).commentTreeNodes.contains
        child := by
  unfold bootstrapCommentTrees at hget ⊢
  apply Std.HashMap.mem_iff_contains.mp
  refine linkReplies_children_subset _ comments _ _ _ ?_ ?_ ref node hget child hchild
  · intro c hc
    exact Std.HashMap.mem_iff_contains.mpr
      ((registerServerCommentIds_commentTreeNodes_contains_iff comments hCommentsHaveBackendIds
        emptyBootstrapState c.ref).mpr (Or.inl ⟨c, hc, rfl⟩))
  · intro ref' node' hget' child' hchild'
    have hempty := registerServerCommentIds_children_empty comments hCommentsHaveBackendIds emptyBootstrapState
      (fun ref'' val'' hget'' => by simp [emptyBootstrapState] at hget'') ref' node' hget'
    rw [hempty] at hchild'
    exact absurd hchild' List.not_mem_nil

private theorem bootstrapCommentTrees_rootMatchesKey
    (comments : List Comment) (hCommentsHaveBackendIds : allCommentsHaveBackendId comments)
    (hParentsInComments : allParentsInComments comments) (ref : CommentRef) (val : CommentThread)
    (hget : (bootstrapCommentTrees comments hCommentsHaveBackendIds hParentsInComments
        emptyBootstrapState (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)).commentTreeNodes[ref]? =
      some val) :
    val.value = ref := by
  unfold bootstrapCommentTrees at hget
  apply linkReplies_rootMatchesKey _ _ _ _ _ _ _ _ hget
  apply registerServerCommentIds_rootMatchesKey
  simp [emptyBootstrapState]

private theorem bootstrapCommentTrees_hasNodeForComment
    (comments : List Comment) (hCommentsHaveBackendIds : allCommentsHaveBackendId comments)
    (hParentsInComments : allParentsInComments comments) (loc : ThreadLocation) (threadRoots : List CommentRef)
    (hpair : (loc, threadRoots) ∈ (bootstrapCommentTrees comments hCommentsHaveBackendIds hParentsInComments
        emptyBootstrapState (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)).locationRoots.toList)
    (ref : CommentRef) (href : ref ∈ threadRoots) :
    (bootstrapCommentTrees comments hCommentsHaveBackendIds hParentsInComments
        emptyBootstrapState (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)).commentTreeNodes.contains
        ref := by
  rw [bootstrapCommentTrees_commentTreeNodes_contains_iff]
  rw [Std.HashMap.mem_toList_iff_getElem?_eq_some] at hpair
  have hmem : ref ∈ (bootstrapCommentTrees comments hCommentsHaveBackendIds hParentsInComments
      emptyBootstrapState (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)).locationRoots.getD loc [] := by
    rw [Std.HashMap.getD_eq_getD_getElem?, hpair]
    simpa using href
  rw [bootstrapCommentTrees_locationRoots_getD_iff] at hmem
  obtain ⟨c, hc, _, hcref, _⟩ := hmem
  exact ⟨c, hc, hcref⟩

/-- Every comment's tree node is reachable from some root, by strong induction on
`createdTimestamp`: a root comment is reachable from itself; a reply's resolved parent has a
strictly earlier timestamp (`hParentsCreatedBefore`), so it is reachable from some root by the
induction hypothesis, and the reply is one more `NodeReachable.step` away via
`bootstrapCommentTrees_children_mem_of_parent`. -/
private theorem assembleCommentTrees_reachable_of_createdTimestamp
    (comments : List Comment) (hCommentsHaveBackendIds : allCommentsHaveBackendId comments)
    (hParentsInComments : allParentsInComments comments)
    (hParentsCreatedBefore : parentsCreatedBefore comments) :
    ∀ n, ∀ c, c ∈ comments → c.createdTimestamp = n →
      ∃ loc threadsList, (loc, threadsList) ∈ (bootstrapCommentTrees comments hCommentsHaveBackendIds
          hParentsInComments emptyBootstrapState
          (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)).locationRoots.toList ∧
        ∃ root ∈ threadsList, CommentThreads.NodeReachable
          (bootstrapCommentTrees comments hCommentsHaveBackendIds hParentsInComments emptyBootstrapState
            (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)).commentTreeNodes root c.ref := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro c hc hn
    rcases h2 : c.parent with _ | parentId
    · have hmemGetD : c.ref ∈ (bootstrapCommentTrees comments hCommentsHaveBackendIds hParentsInComments
          emptyBootstrapState (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)).locationRoots.getD
          c.location.asThreadLocation [] :=
        (bootstrapCommentTrees_locationRoots_getD_iff comments hCommentsHaveBackendIds hParentsInComments
          c.location.asThreadLocation c.ref).mpr ⟨c, hc, h2, rfl, rfl⟩
      rw [Std.HashMap.getD_eq_getD_getElem?] at hmemGetD
      rcases hopt : (bootstrapCommentTrees comments hCommentsHaveBackendIds hParentsInComments
          emptyBootstrapState (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)).locationRoots[
          c.location.asThreadLocation]? with _ | v
      · simp [hopt] at hmemGetD
      · refine ⟨c.location.asThreadLocation, v, Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hopt, c.ref, ?_,
          .refl _⟩
        simpa [hopt] using hmemGetD
    · have hContains : parentId ∈
          (registerServerCommentIds comments hCommentsHaveBackendIds emptyBootstrapState).serverCommentIds :=
        bootstrapParentsHaveNode comments hCommentsHaveBackendIds hParentsInComments emptyBootstrapState c hc
          parentId h2
      rcases registerServerCommentIds_serverCommentIds_getElem?_mem comments hCommentsHaveBackendIds
          emptyBootstrapState parentId _ (Std.HashMap.getElem?_eq_some_getElem hContains) with
          h | ⟨c', hc', hc'backend, hc'ref⟩
      · simp [emptyBootstrapState] at h
      · have hlt : c'.createdTimestamp < c.createdTimestamp :=
          hParentsCreatedBefore c hc parentId h2 c' hc' hc'backend
        obtain ⟨loc, threadsList, hpair, root, hroot, hreach⟩ := ih c'.createdTimestamp (hn ▸ hlt) c' hc' rfl
        refine ⟨loc, threadsList, hpair, root, hroot, ?_⟩
        obtain ⟨node', hnode', hchild⟩ := bootstrapCommentTrees_children_mem_of_parent comments
          hCommentsHaveBackendIds hParentsInComments c hc parentId h2 hContains
        have hparentLive :
            (registerServerCommentIds comments hCommentsHaveBackendIds emptyBootstrapState).serverCommentIds.get
              parentId hContains ∈
              (bootstrapCommentTrees comments hCommentsHaveBackendIds hParentsInComments emptyBootstrapState
                (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)).commentTreeNodes :=
          Std.HashMap.mem_iff_isSome_getElem?.mpr (by rw [hnode']; rfl)
        have hval : (bootstrapCommentTrees comments hCommentsHaveBackendIds hParentsInComments emptyBootstrapState
            (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)).commentTreeNodes.get
              ((registerServerCommentIds comments hCommentsHaveBackendIds emptyBootstrapState).serverCommentIds.get
                parentId hContains) hparentLive = node' :=
          Option.some.inj (((Std.HashMap.getElem?_eq_some_getElem hparentLive).symm).trans hnode')
        refine (hc'ref ▸ hreach).step hparentLive ?_
        exact hval ▸ hchild

private theorem commentsAllInSameFileOrAllTopLevel_dichotomy {comments : List Comment}
    (h : commentsAllInSameFileOrAllTopLevel comments) :
    (∀ c, c ∈ comments → c.location.asThreadLocation = .topLevel) ∨
      (∀ c, c ∈ comments → c.location.asThreadLocation ≠ .topLevel) := by
  rcases h with h | h | h
  · refine Or.inl fun c hc => ?_
    rcases hloc : c.location with loc | _
    · exact absurd (h c hc) (by simp [hloc, CommentLocation.isTopLevel])
    · rfl
  · refine Or.inr fun c hc => ?_
    obtain ⟨loc, hloc, _⟩ := h c hc
    simp [hloc, CommentLocation.asThreadLocation]
  · refine Or.inr fun c hc => ?_
    obtain ⟨loc, hloc, _⟩ := h c hc
    simp [hloc, CommentLocation.asThreadLocation]

private theorem length_le_one_of_nodup_of_forall_eq {α : Type} {l : List α} {a : α}
    (hNodup : l.Nodup) (hAll : ∀ x, x ∈ l → x = a) : l.length ≤ 1 := by
  match l with
  | [] => simp
  | [_] => simp
  | x :: y :: rest =>
    exfalso
    have hxy : x = y := (hAll x (by simp)).trans (hAll y (by simp)).symm
    rw [List.nodup_cons] at hNodup
    exact hNodup.1 (hxy ▸ List.mem_cons_self)

private theorem assembleCommentTrees_hLocationsConsistent
    (comments : List Comment) (hSameLocation : commentsAllInSameFileOrAllTopLevel comments)
    (hCommentsHaveBackendIds : allCommentsHaveBackendId comments)
    (hParentsInComments : allParentsInComments comments) :
    (∀ loc, loc ∈ (bootstrapCommentTrees comments hCommentsHaveBackendIds hParentsInComments
        emptyBootstrapState (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)).locationRoots.keys →
      loc.isTopLevel ∧ (bootstrapCommentTrees comments hCommentsHaveBackendIds hParentsInComments
        emptyBootstrapState (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)).locationRoots.size = 1) ∨
      (∀ loc, loc ∈ (bootstrapCommentTrees comments hCommentsHaveBackendIds hParentsInComments
        emptyBootstrapState (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)).locationRoots.keys →
        ¬ loc.isTopLevel) := by
  rcases commentsAllInSameFileOrAllTopLevel_dichotomy hSameLocation with hAll | hAll
  · refine Or.inl fun loc hloc => ?_
    obtain ⟨c, hc, _, hcloc⟩ := bootstrapCommentTrees_locationRoots_mem_of_mem comments
      hCommentsHaveBackendIds hParentsInComments loc (Std.HashMap.mem_keys.mp hloc)
    have hlocEq : loc = ThreadLocation.topLevel := hcloc ▸ hAll c hc
    subst hlocEq
    refine ⟨rfl, ?_⟩
    have hle := length_le_one_of_nodup_of_forall_eq (a := ThreadLocation.topLevel) Std.HashMap.nodup_keys
      (fun loc' hloc' => by
        obtain ⟨c', hc', _, hc'loc⟩ := bootstrapCommentTrees_locationRoots_mem_of_mem comments
          hCommentsHaveBackendIds hParentsInComments loc' (Std.HashMap.mem_keys.mp hloc')
        exact hc'loc ▸ hAll c' hc')
    have hge := List.length_pos_of_mem hloc
    rw [Std.HashMap.length_keys] at hle hge
    omega
  · refine Or.inr fun loc hloc => ?_
    obtain ⟨c, hc, _, hcloc⟩ := bootstrapCommentTrees_locationRoots_mem_of_mem comments
      hCommentsHaveBackendIds hParentsInComments loc (Std.HashMap.mem_keys.mp hloc)
    have hne : loc ≠ ThreadLocation.topLevel := hcloc ▸ hAll c hc
    cases loc with
    | topLevel => exact absurd rfl hne
    | lineNumber _ => simp [ThreadLocation.isTopLevel]

/- Assemble a list of comments into their respective threads.

This creates trees of comments with each tree rooted at a comment with a known location.

All of the comments must be in the same file or all be top-level comments.

Note that this function is only used when receiving new comments from the server.  In that context,
all of the comments should have a backend id.  We use that when constructing the
serverCommentIds map.  Comments are added to the tree separately (but even then they have a backend
id since we only add them to the tree after we get the id from the server).

 -/
def assembleCommentTrees (comments : List Comment)
                         (hSameLocation : commentsAllInSameFileOrAllTopLevel comments)
                         (hCommentsHaveBackendIds : allCommentsHaveBackendId comments)
                         (hParentsInComments : allParentsInComments comments)
                         (hRefsNodup : commentRefsNodup comments)
                         (hParentsCreatedBefore : parentsCreatedBefore comments)
                         : CommentThreads :=
  let finalState := bootstrapCommentTrees comments hCommentsHaveBackendIds hParentsInComments
    emptyBootstrapState (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)
  { commentTreeNodes := finalState.commentTreeNodes,
    serverCommentIds := finalState.serverCommentIds,
    locationRoots := finalState.locationRoots,
    hLocationsConsistent :=
      assembleCommentTrees_hLocationsConsistent comments hSameLocation hCommentsHaveBackendIds hParentsInComments,
    hHasNodeForComment := fun loc threadRoots hpair ref href =>
      bootstrapCommentTrees_hasNodeForComment comments hCommentsHaveBackendIds hParentsInComments loc threadRoots
        hpair ref href,
    hAllCommentTreeNodesAreLive := fun commentRef hmem => by
      obtain ⟨c, hc, hcref⟩ := (bootstrapCommentTrees_commentTreeNodes_contains_iff comments
        hCommentsHaveBackendIds hParentsInComments commentRef).mp (Std.HashMap.mem_keys.mp hmem)
      obtain ⟨loc, threadsList, hpair, root, hroot, hreach⟩ :=
        assembleCommentTrees_reachable_of_createdTimestamp comments hCommentsHaveBackendIds hParentsInComments
          hParentsCreatedBefore c.createdTimestamp c hc rfl
      exact ⟨loc, threadsList, hpair, root, hroot, hcref ▸ hreach⟩,
    hCommentTreeNodeRootMatchesKey := fun ref h =>
      bootstrapCommentTrees_rootMatchesKey comments hCommentsHaveBackendIds hParentsInComments ref
        (finalState.commentTreeNodes.get ref h)
        (Std.HashMap.getElem?_eq_some_getElem (Std.HashMap.mem_iff_contains.mpr h)),
    hLocationRootsNodup :=
      bootstrapCommentTrees_locationRootsNodup comments hCommentsHaveBackendIds hParentsInComments hRefsNodup,
    hChildrenAreRegistered := fun ref h child hchild =>
      bootstrapCommentTrees_children_registered comments hCommentsHaveBackendIds hParentsInComments ref
        (finalState.commentTreeNodes.get ref h)
        (Std.HashMap.getElem?_eq_some_getElem (Std.HashMap.mem_iff_contains.mpr h)) child hchild
    }

def addCommentToThread (commentThreads : CommentThreads) (comment : Comment) : Unit := sorry
