module

import Std

public import LgtmLean.Basic
import all LgtmLean.Basic
import all LgtmLean.Tree

public def commentsAllInSameFileOrAllTopLevel (comments : List Comment) : Prop :=
  (∀ c, c ∈ comments → c.location.isTopLevel) ∨
  (∀ c, c ∈ comments → ∃ loc, c.location = .fileLocation loc ∧ loc.version = .base) ∨
  (∀ c, c ∈ comments → ∃ loc, c.location = .fileLocation loc ∧ loc.version = .current)

public def allCommentsHaveBackendId (comments : List Comment) : Prop := ∀ c, c ∈ comments → c.backendId.isSome

/-- Every parent referenced by a comment in the batch is itself the backend id of some comment in
the batch.  This is needed to look the parent up in `serverCommentIds` while assembling threads. -/
public def allParentsInComments (comments : List Comment) : Prop :=
  ∀ c, c ∈ comments → ∀ parentId, c.parent = some parentId → ∃ c', c' ∈ comments ∧ c'.backendId = some parentId

/-- Every comment in the batch has a distinct `ref`, so no `CommentRef` is ever pushed twice into
`locationRoots`. -/
public def commentRefsNodup (comments : List Comment) : Prop := (comments.map Comment.ref).Nodup

/-- A reply's parent was created strictly before it. This rules out cycles in the batch's `parent`
links, which is needed to show every comment's tree node is reachable from some root. -/
public def parentsCreatedBefore (comments : List Comment) : Prop :=
  ∀ c, c ∈ comments → ∀ parentId, c.parent = some parentId →
    ∀ c', c' ∈ comments → c'.backendId = some parentId → c'.createdTimestamp < c.createdTimestamp

/-- The non-automatically-decidable piece of `commentsAllInSameFileOrAllTopLevel`: the existential
quantifies over all of `CommentFileLocation`, which is infinite, but it's actually just a case
split on `c.location` in disguise (the `∃ loc` is pinned down by the equation). -/
public instance existsFileLocationVersion.decidable (c : Comment) (v : FileVersion) :
    Decidable (∃ loc, c.location = .fileLocation loc ∧ loc.version = v) :=
  match hloc : c.location with
  | .topLevel => .isFalse (fun ⟨_, h, _⟩ => by cases h)
  | .fileLocation loc =>
    if hv : loc.version = v then .isTrue ⟨loc, rfl, hv⟩
    else .isFalse (fun ⟨loc', h, hv'⟩ => by cases h; exact hv hv')

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

/-- `linkReplies` preserves the invariant that every registered `serverCommentIds` entry has a
matching `commentTreeNodes` entry: it never modifies `serverCommentIds` (only ever updates
`commentTreeNodes`/`locationRoots` via `{ s with ... }`), so the fixed `serverCommentIds` argument
stays exactly `s.serverCommentIds` throughout, and its `hInv`-style invariant propagates unchanged
to the final state. -/
private theorem linkReplies_serverCommentIds_registered (serverCommentIds : Std.HashMap ServerId CommentRef) :
    (comments : List Comment) →
    (hParentsHaveNode : ∀ c, c ∈ comments → ∀ parentId, c.parent = some parentId → parentId ∈ serverCommentIds) →
    (s : CommentTreeBootstrapState) →
    (hInv : ∀ sid (h : sid ∈ serverCommentIds), serverCommentIds.get sid h ∈ s.commentTreeNodes) →
    (hSEq : s.serverCommentIds = serverCommentIds) →
    ∀ sid (h : (linkReplies serverCommentIds comments hParentsHaveNode s hInv).serverCommentIds.contains sid),
      (linkReplies serverCommentIds comments hParentsHaveNode s hInv).commentTreeNodes.contains
        ((linkReplies serverCommentIds comments hParentsHaveNode s hInv).serverCommentIds.get sid h)
  | [], _, s, hInv, hSEq => by
    rw [linkReplies_nil]
    intro sid h
    subst hSEq
    exact hInv sid h
  | comment :: rest, hParentsHaveNode, s, hInv, hSEq => by
    rcases h2 : comment.parent with _ | parentId
    · let newLocationRoots := s.locationRoots.alter comment.location.asThreadLocation (insertSingletonOrAppend comment.ref)
      let s' : CommentTreeBootstrapState := { s with locationRoots := newLocationRoots }
      rw [linkReplies_cons_none serverCommentIds comment rest h2 hParentsHaveNode s hInv]
      exact linkReplies_serverCommentIds_registered serverCommentIds rest _ s' hInv hSEq
    · have hContains : parentId ∈ serverCommentIds := hParentsHaveNode comment List.mem_cons_self parentId h2
      let parentTreeNode := s.commentTreeNodes.get (serverCommentIds.get parentId hContains) (hInv parentId hContains)
      let s' : CommentTreeBootstrapState :=
        { s with commentTreeNodes :=
            s.commentTreeNodes.insert (serverCommentIds.get parentId hContains) (parentTreeNode.addChild comment.ref) }
      rw [linkReplies_cons_some serverCommentIds comment rest parentId h2 hParentsHaveNode s hInv hContains]
      exact linkReplies_serverCommentIds_registered serverCommentIds rest _ s'
        (fun sid h => Std.HashMap.mem_insert.mpr (Or.inr (hInv sid h))) hSEq

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

/-- Every server-tracked comment id `bootstrapCommentTrees` produces has a matching tree node:
`registerServerCommentIds` establishes it for the intermediate state (`bootstrapCommentTreeNodesInv`),
and `linkReplies` never touches `serverCommentIds`, so it survives unchanged to the final state
(`linkReplies_serverCommentIds_registered`). -/
private theorem bootstrapCommentTrees_serverCommentIdsRegistered
    (comments : List Comment) (hCommentsHaveBackendIds : allCommentsHaveBackendId comments)
    (hParentsInComments : allParentsInComments comments) :
    ∀ sid (h : (bootstrapCommentTrees comments hCommentsHaveBackendIds hParentsInComments
        emptyBootstrapState (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)).serverCommentIds.contains
        sid),
      (bootstrapCommentTrees comments hCommentsHaveBackendIds hParentsInComments
        emptyBootstrapState (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)).commentTreeNodes.contains
        ((bootstrapCommentTrees comments hCommentsHaveBackendIds hParentsInComments
          emptyBootstrapState (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)).serverCommentIds.get
          sid h) := by
  unfold bootstrapCommentTrees
  exact linkReplies_serverCommentIds_registered _ comments _ _
    (bootstrapCommentTreeNodesInv comments hCommentsHaveBackendIds emptyBootstrapState
      (fun _sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)) rfl

/- Assemble a list of comments into their respective threads.

This creates trees of comments with each tree rooted at a comment with a known location.

All of the comments must be in the same file or all be top-level comments.

Note that this function is only used when receiving new comments from the server.  In that context,
all of the comments should have a backend id.  We use that when constructing the
serverCommentIds map.  Comments are added to the tree separately (but even then they have a backend
id since we only add them to the tree after we get the id from the server).

 -/
public def assembleCommentTrees (comments : List Comment)
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
        (Std.HashMap.getElem?_eq_some_getElem (Std.HashMap.mem_iff_contains.mpr h)) child hchild,
    hServerCommentIdsRegistered :=
      bootstrapCommentTrees_serverCommentIdsRegistered comments hCommentsHaveBackendIds hParentsInComments
    }

/-- The batch-assembly counterpart of `addCommentToThread_locationRoots_isTopLevel`: if every
comment in the batch is top-level, every `ThreadLocation` key registered in the resulting
`CommentThreads.locationRoots` is top-level too. `hSameLocation` is taken as a separate opaque
hypothesis (rather than requiring the literal term `Or.inl hAllTopLevel`) so that callers can
supply whichever proof they already have of it. Needed by `addRemoteComments` to reestablish
`CommentManager.hTopLevelThreadsAllTopLevel` after bulk-loading comments from the server. -/
public theorem assembleCommentTrees_locationRoots_isTopLevel
    (comments : List Comment) (hSameLocation : commentsAllInSameFileOrAllTopLevel comments)
    (hAllTopLevel : ∀ c, c ∈ comments → c.location.isTopLevel)
    (hCommentsHaveBackendIds : allCommentsHaveBackendId comments)
    (hParentsInComments : allParentsInComments comments)
    (hRefsNodup : commentRefsNodup comments)
    (hParentsCreatedBefore : parentsCreatedBefore comments) :
    ∀ loc, loc ∈ (assembleCommentTrees comments hSameLocation hCommentsHaveBackendIds hParentsInComments
        hRefsNodup hParentsCreatedBefore).locationRoots.keys → loc.isTopLevel = true := by
  intro loc hloc
  unfold assembleCommentTrees at hloc
  obtain ⟨c, hc, _, hcloc⟩ := bootstrapCommentTrees_locationRoots_mem_of_mem comments
    hCommentsHaveBackendIds hParentsInComments loc (Std.HashMap.mem_keys.mp hloc)
  have hctop : c.location = CommentLocation.topLevel := by
    cases hloc' : c.location with
    | topLevel => rfl
    | fileLocation loc' =>
      exfalso
      have h := hAllTopLevel c hc
      rw [hloc', CommentLocation.fileLocation_isTopLevel] at h
      exact absurd h (by decide)
  rw [hctop] at hcloc
  have hloceq : loc = ThreadLocation.topLevel := hcloc.symm.trans rfl
  rw [hloceq]
  rfl

/-- A ref is registered as a tree node in `assembleCommentTrees`'s output iff some comment in the
batch has that ref -- the public counterpart of `bootstrapCommentTrees_commentTreeNodes_contains_iff`.
Needed by `addRemoteComments` to reestablish `CommentManager.hTopLevelThreadsPublished` after
bulk-loading comments from the server. -/
public theorem assembleCommentTrees_commentTreeNodes_contains_iff
    (comments : List Comment) (hSameLocation : commentsAllInSameFileOrAllTopLevel comments)
    (hCommentsHaveBackendIds : allCommentsHaveBackendId comments)
    (hParentsInComments : allParentsInComments comments)
    (hRefsNodup : commentRefsNodup comments)
    (hParentsCreatedBefore : parentsCreatedBefore comments) (ref : CommentRef) :
    (assembleCommentTrees comments hSameLocation hCommentsHaveBackendIds hParentsInComments
        hRefsNodup hParentsCreatedBefore).commentTreeNodes.contains ref ↔
      ∃ c, c ∈ comments ∧ c.ref = ref := by
  unfold assembleCommentTrees
  exact bootstrapCommentTrees_commentTreeNodes_contains_iff comments hCommentsHaveBackendIds hParentsInComments ref

private theorem isSome_insertSingletonOrAppend (value : α) (current : Option (List α)) :
    (insertSingletonOrAppend value current).isSome = true := by
  cases current <;> simp [insertSingletonOrAppend]

private theorem ThreadLocation.isTopLevel_eq_true_iff {l : ThreadLocation} :
    l.isTopLevel = true ↔ l = .topLevel := by
  cases l <;> simp [ThreadLocation.isTopLevel]

/-- Inserting a new ref at `loc` (via `alter`/`insertSingletonOrAppend`) preserves
`CommentThreads.hLocationsConsistent`, provided `loc`'s top-level-ness matches whatever's already
in `locationRoots` (`hScope`). Used by `addCommentToThread`'s `none`-parent branch, where `loc` may
be a brand-new key. -/
private theorem hLocationsConsistent_alter
    (locationRoots : Std.HashMap ThreadLocation (List CommentRef))
    (loc : ThreadLocation) (ref : CommentRef)
    (hConsistent : (∀ l, l ∈ locationRoots.keys → l.isTopLevel = true ∧ locationRoots.size = 1) ∨
                   (∀ l, l ∈ locationRoots.keys → ¬ l.isTopLevel = true))
    (hScope : ∀ l, l ∈ locationRoots.keys → l.isTopLevel = loc.isTopLevel) :
    (∀ l, l ∈ (locationRoots.alter loc (insertSingletonOrAppend ref)).keys →
        l.isTopLevel = true ∧ (locationRoots.alter loc (insertSingletonOrAppend ref)).size = 1) ∨
    (∀ l, l ∈ (locationRoots.alter loc (insertSingletonOrAppend ref)).keys → ¬ l.isTopLevel = true) := by
  by_cases hTop : loc.isTopLevel = true
  · left
    have hEqLoc : ∀ l, l ∈ locationRoots.keys → l = loc := by
      intro l hl
      have h1 : l.isTopLevel = true := (hScope l hl).trans hTop
      rw [ThreadLocation.isTopLevel_eq_true_iff] at h1
      rw [ThreadLocation.isTopLevel_eq_true_iff] at hTop
      rw [h1, hTop]
    have hSize : (locationRoots.alter loc (insertSingletonOrAppend ref)).size = 1 := by
      by_cases hmem : loc ∈ locationRoots
      · have hmemKeys : loc ∈ locationRoots.keys := Std.HashMap.mem_keys.mpr hmem
        rw [Std.HashMap.size_alter_eq_self_of_mem hmem (isSome_insertSingletonOrAppend _ _)]
        rcases hConsistent with hc | hc
        · exact (hc loc hmemKeys).2
        · exact absurd (hc loc hmemKeys) (by simp [hTop])
      · rw [Std.HashMap.size_alter_eq_add_one hmem (isSome_insertSingletonOrAppend _ _)]
        have hnotmem : ∀ a, ¬ a ∈ locationRoots := fun a ha =>
          hmem (hEqLoc a (Std.HashMap.mem_keys.mpr ha) ▸ ha)
        have hempty : locationRoots.isEmpty = true := Std.HashMap.isEmpty_iff_forall_not_mem.mpr hnotmem
        rw [Std.HashMap.isEmpty_eq_size_eq_zero] at hempty
        have hzero : locationRoots.size = 0 := beq_iff_eq.mp hempty
        omega
    intro l hl
    rw [Std.HashMap.mem_keys, Std.HashMap.mem_alter] at hl
    refine ⟨?_, hSize⟩
    by_cases hbeq : loc == l
    · have heq : l = loc := (beq_iff_eq.mp hbeq).symm
      rw [heq]; exact hTop
    · simp only [hbeq] at hl
      exact (hScope l (Std.HashMap.mem_keys.mpr hl)).trans hTop
  · right
    intro l hl
    rw [Std.HashMap.mem_keys, Std.HashMap.mem_alter] at hl
    by_cases hbeq : loc == l
    · have heq : l = loc := (beq_iff_eq.mp hbeq).symm
      rw [heq]; exact hTop
    · simp only [hbeq] at hl
      rw [hScope l (Std.HashMap.mem_keys.mpr hl)]
      exact hTop

private theorem mem_getD_iff_exists_mem_toList
    (m : Std.HashMap ThreadLocation (List CommentRef)) (k : ThreadLocation) (ref : CommentRef) :
    ref ∈ m.getD k [] ↔ ∃ v, (k, v) ∈ m.toList ∧ ref ∈ v := by
  constructor
  · intro h
    rw [Std.HashMap.getD_eq_getD_getElem?] at h
    rcases hk : m[k]? with _ | v
    · rw [hk] at h; simp at h
    · rw [hk] at h
      simp only [Option.getD_some] at h
      exact ⟨v, Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hk, h⟩
  · rintro ⟨v, hv, href⟩
    have hk : m[k]? = some v := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hv
    rw [Std.HashMap.getD_eq_getD_getElem?, hk]
    simp [href]

/-- Inserting a new ref at `loc` (via `alter`/`insertSingletonOrAppend`) preserves
`CommentThreads.hHasNodeForComment`, as long as the tree-node map only grows (`hMono`) and the new
ref is already registered in the new tree-node map (`hRefRegistered`). Used by
`addCommentToThread`'s `none`-parent branch. -/
private theorem hHasNodeForComment_alter
    (locationRoots : Std.HashMap ThreadLocation (List CommentRef))
    (oldTreeNodes newTreeNodes : Std.HashMap CommentRef CommentThread)
    (loc : ThreadLocation) (ref : CommentRef)
    (hHasNode : ∀ loc' threadRoots', (loc', threadRoots') ∈ locationRoots.toList →
      ∀ ref', ref' ∈ threadRoots' → oldTreeNodes.contains ref')
    (hMono : ∀ x, oldTreeNodes.contains x → newTreeNodes.contains x)
    (hRefRegistered : newTreeNodes.contains ref) :
    ∀ loc' threadRoots', (loc', threadRoots') ∈ (locationRoots.alter loc (insertSingletonOrAppend ref)).toList →
      ∀ ref', ref' ∈ threadRoots' → newTreeNodes.contains ref' := by
  intro loc' threadRoots' hpair ref' href'
  have hg : (locationRoots.alter loc (insertSingletonOrAppend ref)).getD loc' [] = threadRoots' := by
    rw [Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hpair]
    simp
  have href'' : ref' ∈ (locationRoots.alter loc (insertSingletonOrAppend ref)).getD loc' [] := hg ▸ href'
  rw [mem_getD_alter_insertSingletonOrAppend] at href''
  rcases href'' with ⟨_, heq⟩ | hold
  · rw [heq]; exact hRefRegistered
  · obtain ⟨v, hv, hmemv⟩ := (mem_getD_iff_exists_mem_toList locationRoots loc' ref').mp hold
    exact hMono ref' (hHasNode loc' v hv ref' hmemv)

private theorem contains_mono_insert {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : Std.HashMap α β) (k : α) (v : β) :
    ∀ x, m.contains x = true → (m.insert k v).contains x = true := by
  intro x hx
  rw [Std.HashMap.contains_insert, hx, Bool.or_true]

/-- Inserting a key/value pair whose value's `.value` field matches the key preserves
`CommentThreads.hCommentTreeNodeRootMatchesKey`. -/
private theorem hCommentTreeNodeRootMatchesKey_insert
    (m : Std.HashMap CommentRef CommentThread) (k : CommentRef) (v : CommentThread)
    (hv : v.value = k)
    (hOld : ∀ ref (h : m.contains ref), (m.get ref h).value = ref) :
    ∀ ref (h : (m.insert k v).contains ref), ((m.insert k v).get ref h).value = ref := by
  intro ref h
  have hmem : ref ∈ m.insert k v := h
  show ((m.insert k v).get ref hmem).value = ref
  rw [Std.HashMap.get_eq_getElem, Std.HashMap.getElem_insert]
  split
  · next hbeq => rw [beq_iff_eq] at hbeq; rw [← hbeq]; exact hv
  · next hbeq =>
    have hcontains : m.contains ref := Std.HashMap.contains_of_contains_insert h (by simpa using hbeq)
    exact hOld ref hcontains

/-- Inserting a new ref at `loc` (via `alter`/`insertSingletonOrAppend`) preserves
`CommentThreads.hLocationRootsNodup`, as long as the ref is not already registered anywhere in
`commentTreeNodes` (`hRefFresh`) -- combined with `hHasNode`, that rules out the ref already
appearing among the existing thread roots. -/
private theorem hLocationRootsNodup_alter
    (locationRoots : Std.HashMap ThreadLocation (List CommentRef))
    (commentTreeNodes : Std.HashMap CommentRef CommentThread)
    (loc : ThreadLocation) (ref : CommentRef)
    (hHasNode : ∀ loc' threadRoots', (loc', threadRoots') ∈ locationRoots.toList →
      ∀ ref', ref' ∈ threadRoots' → commentTreeNodes.contains ref')
    (hRefFresh : ref ∉ commentTreeNodes)
    (hOldNodup : (locationRoots.toList.flatMap Prod.snd).Nodup) :
    ((locationRoots.alter loc (insertSingletonOrAppend ref)).toList.flatMap Prod.snd).Nodup := by
  have hperm := flatMap_snd_toList_alter_insertSingletonOrAppend_perm locationRoots loc ref
  rw [hperm.nodup_iff, List.nodup_cons]
  refine ⟨?_, hOldNodup⟩
  intro hmem
  rw [List.mem_flatMap] at hmem
  obtain ⟨⟨loc', threadRoots'⟩, hpair, href⟩ := hmem
  exact hRefFresh (Std.HashMap.mem_iff_contains.mpr (hHasNode loc' threadRoots' hpair ref href))

/-- Inserting a key/value pair whose children are all registered in the resulting map preserves
`CommentThreads.hChildrenAreRegistered`. -/
private theorem hChildrenAreRegistered_insert
    (m : Std.HashMap CommentRef CommentThread) (k : CommentRef) (v : CommentThread)
    (hvChildren : ∀ child, child ∈ v.children → (m.insert k v).contains child)
    (hOld : ∀ ref (h : m.contains ref) child, child ∈ (m.get ref h).children → m.contains child) :
    ∀ ref (h : (m.insert k v).contains ref) child, child ∈ ((m.insert k v).get ref h).children →
      (m.insert k v).contains child := by
  intro ref h child hchild
  have hmem : ref ∈ m.insert k v := h
  have hchild' : child ∈ ((m.insert k v)[ref]'hmem).children := hchild
  rw [Std.HashMap.getElem_insert] at hchild'
  split at hchild'
  · next hbeq => exact hvChildren child hchild'
  · next hbeq =>
    have hcontains : m.contains ref := Std.HashMap.contains_of_contains_insert h (by simpa using hbeq)
    have hres := hOld ref hcontains child hchild'
    rw [Std.HashMap.contains_insert, hres, Bool.or_true]

/-- `NodeReachable` is monotone under any change to the tree-node map that only grows each
registered node's `children` list (and keeps every previously-registered node registered). Used to
transport reachability proofs from `commentThreads` across `addCommentToThread`'s tree-node
updates. -/
private theorem NodeReachable_mono
    {oldNodes newNodes : Std.HashMap CommentRef CommentThread}
    (hMono : ∀ ref (h : oldNodes.contains ref), ∃ h' : newNodes.contains ref,
        (oldNodes.get ref h).children ⊆ (newNodes.get ref h').children)
    {root ref : CommentRef} (hReach : CommentThreads.NodeReachable oldNodes root ref) :
    CommentThreads.NodeReachable newNodes root ref := by
  induction hReach with
  | refl => exact CommentThreads.NodeReachable.refl root
  | step h hparent hchild ih =>
    obtain ⟨hparent', hsub⟩ := hMono _ hparent
    exact CommentThreads.NodeReachable.step ih hparent' (hsub hchild)

/-- Inserting at a key different from `ref` leaves `ref`'s stored node (hence its children)
completely unchanged. -/
private theorem children_subset_insert_of_ne
    (m : Std.HashMap CommentRef CommentThread) (k ref : CommentRef) (v : CommentThread)
    (h : m.contains ref) (hne : ¬ k = ref) :
    ∃ h' : (m.insert k v).contains ref, (m.get ref h).children ⊆ ((m.insert k v).get ref h').children := by
  have hmem : ref ∈ m.insert k v := by
    rw [Std.HashMap.mem_insert]; right; exact Std.HashMap.mem_iff_contains.mpr h
  refine ⟨hmem, ?_⟩
  have heq : ((m.insert k v).get ref hmem) = m.get ref h := by
    show ((m.insert k v)[ref]'hmem) = m[ref]'(Std.HashMap.mem_iff_contains.mpr h)
    rw [Std.HashMap.getElem_insert]
    have hbeqfalse : (k == ref) = false := by
      rw [Bool.eq_false_iff]
      intro hc
      exact hne (beq_iff_eq.mp hc)
    simp [hbeqfalse]
  rw [heq]
  exact fun _ hx => hx

/-- After `alter loc (insertSingletonOrAppend ref)`, any pre-existing `(loc', threadsList')` pair
survives (unchanged if `loc' ≠ loc`, with `ref` prepended if `loc' = loc`) -- in particular any
element already in `threadsList'` is still findable in some pair's list. Used to transport
`hAllCommentTreeNodesAreLive` witnesses across the `none`-parent branch's `locationRoots` update. -/
private theorem locationRoots_pair_alter_mem
    (m : Std.HashMap ThreadLocation (List CommentRef)) (loc loc' : ThreadLocation) (ref root : CommentRef)
    (threadsList' : List CommentRef) (hpair : (loc', threadsList') ∈ m.toList) (hroot : root ∈ threadsList') :
    ∃ threadsList'', (loc', threadsList'') ∈ (m.alter loc (insertSingletonOrAppend ref)).toList ∧ root ∈ threadsList'' := by
  by_cases heq : loc = loc'
  · subst heq
    refine ⟨ref :: threadsList', ?_, List.mem_cons_of_mem _ hroot⟩
    have hget : m[loc]? = some threadsList' := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hpair
    have hget2 : (m.alter loc (insertSingletonOrAppend ref))[loc]? = some (ref :: threadsList') := by
      rw [Std.HashMap.getElem?_alter]
      simp [hget, insertSingletonOrAppend]
    exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hget2
  · refine ⟨threadsList', ?_, hroot⟩
    have hget : m[loc']? = some threadsList' := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hpair
    have hget2 : (m.alter loc (insertSingletonOrAppend ref))[loc']? = some threadsList' := by
      rw [Std.HashMap.getElem?_alter]
      have hbeqfalse : (loc == loc') = false := by
        rw [Bool.eq_false_iff]; intro hc; exact heq (beq_iff_eq.mp hc)
      simp [hbeqfalse, hget]
    exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hget2

/-- `CommentThreads.hAllCommentTreeNodesAreLive` survives adding a fresh leaf node `ref` (with tree
node `treeNode`) to `commentTreeNodes` and registering it as a thread root at `loc` (via
`alter`/`insertSingletonOrAppend`). Used by `addCommentToThread`'s `none`-parent branch, where the
new comment becomes its own root. -/
private theorem hAllCommentTreeNodesAreLive_alter
    (commentThreads : CommentThreads) (ref : CommentRef) (treeNode : CommentThread) (loc : ThreadLocation)
    (hRefFresh : ref ∉ commentThreads.commentTreeNodes) :
    ∀ commentRef, commentRef ∈ (commentThreads.commentTreeNodes.insert ref treeNode).keys →
      ∃ loc' threadsList, (loc', threadsList) ∈
          (commentThreads.locationRoots.alter loc (insertSingletonOrAppend ref)).toList ∧
        ∃ root ∈ threadsList,
          CommentThreads.NodeReachable (commentThreads.commentTreeNodes.insert ref treeNode) root commentRef := by
  let treeNodesWithThis := commentThreads.commentTreeNodes.insert ref treeNode
  have hMono : ∀ r (h : commentThreads.commentTreeNodes.contains r),
      ∃ h' : treeNodesWithThis.contains r,
        (commentThreads.commentTreeNodes.get r h).children ⊆ (treeNodesWithThis.get r h').children := by
    intro r h
    exact children_subset_insert_of_ne commentThreads.commentTreeNodes ref r treeNode h
      (fun heq => hRefFresh (heq ▸ Std.HashMap.mem_iff_contains.mpr h))
  intro commentRef hmem
  rw [Std.HashMap.mem_keys, Std.HashMap.mem_insert] at hmem
  rcases hmem with heq | hold
  · have heq' : ref = commentRef := beq_iff_eq.mp heq
    subst heq'
    have hnewget : (commentThreads.locationRoots.alter loc (insertSingletonOrAppend ref))[loc]? =
        insertSingletonOrAppend ref commentThreads.locationRoots[loc]? := by
      rw [Std.HashMap.getElem?_alter]; simp
    rcases hcur : commentThreads.locationRoots[loc]? with _ | oldList
    · refine ⟨loc, [ref], ?_, ref, List.mem_singleton_self _, CommentThreads.NodeReachable.refl _⟩
      have hfin : (commentThreads.locationRoots.alter loc (insertSingletonOrAppend ref))[loc]? =
          some [ref] := by rw [hnewget, hcur]; rfl
      exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hfin
    · refine ⟨loc, ref :: oldList, ?_, ref, List.mem_cons_self, CommentThreads.NodeReachable.refl _⟩
      have hfin : (commentThreads.locationRoots.alter loc (insertSingletonOrAppend ref))[loc]? =
          some (ref :: oldList) := by rw [hnewget, hcur]; rfl
      exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hfin
  · obtain ⟨loc', threadsList', hpair, root, hrootmem, hreach⟩ :=
      commentThreads.hAllCommentTreeNodesAreLive commentRef (Std.HashMap.mem_keys.mpr hold)
    obtain ⟨threadsList'', hpair'', hrootmem''⟩ :=
      locationRoots_pair_alter_mem commentThreads.locationRoots loc loc' ref root threadsList' hpair hrootmem
    exact ⟨loc', threadsList'', hpair'', root, hrootmem'', NodeReachable_mono hMono hreach⟩

/-- `CommentThreads.hAllCommentTreeNodesAreLive` survives adding a fresh leaf node `ref` (with tree
node `treeNode`) and threading it in as a new child of an already-registered `parentThreadRef`
(whose stored node is updated to `updatedParentThread`, gaining `ref` as its first child).
`locationRoots` is untouched, since a reply isn't a new thread root. Used by
`addCommentToThread`'s `some`-parent branch. -/
private theorem hAllCommentTreeNodesAreLive_insert_reply
    (commentThreads : CommentThreads) (ref : CommentRef) (treeNode : CommentThread)
    (parentThreadRef : CommentRef) (hMemTree : commentThreads.commentTreeNodes.contains parentThreadRef)
    (updatedParentThread : CommentThread)
    (hUpdatedChildren : updatedParentThread.children =
      ref :: (commentThreads.commentTreeNodes.get parentThreadRef hMemTree).children)
    (hRefFresh : ref ∉ commentThreads.commentTreeNodes) :
    ∀ commentRef, commentRef ∈
        ((commentThreads.commentTreeNodes.insert ref treeNode).insert parentThreadRef updatedParentThread).keys →
      ∃ loc threadsList, (loc, threadsList) ∈ commentThreads.locationRoots.toList ∧
        ∃ root ∈ threadsList, CommentThreads.NodeReachable
          ((commentThreads.commentTreeNodes.insert ref treeNode).insert parentThreadRef updatedParentThread)
          root commentRef := by
  let treeNodesWithThis := commentThreads.commentTreeNodes.insert ref treeNode
  have hMonoOldToFinal : ∀ r (h : commentThreads.commentTreeNodes.contains r),
      ∃ h' : (treeNodesWithThis.insert parentThreadRef updatedParentThread).contains r,
        (commentThreads.commentTreeNodes.get r h).children ⊆
          ((treeNodesWithThis.insert parentThreadRef updatedParentThread).get r h').children := by
    intro r h
    by_cases hrefeq : r = parentThreadRef
    · subst hrefeq
      have hfmem : r ∈ treeNodesWithThis.insert r updatedParentThread :=
        Std.HashMap.mem_insert_self
      refine ⟨hfmem, ?_⟩
      have hget : (treeNodesWithThis.insert r updatedParentThread).get r hfmem =
          updatedParentThread := by
        show (treeNodesWithThis.insert r updatedParentThread)[r]'hfmem = updatedParentThread
        exact Std.HashMap.getElem_insert_self
      rw [hget, hUpdatedChildren]
      exact List.subset_cons_self _ _
    · obtain ⟨h1, hsub1⟩ := children_subset_insert_of_ne commentThreads.commentTreeNodes ref r
        treeNode h (fun heq => hRefFresh (heq ▸ Std.HashMap.mem_iff_contains.mpr h))
      obtain ⟨h2, hsub2⟩ := children_subset_insert_of_ne treeNodesWithThis parentThreadRef r
        updatedParentThread h1 (fun heq => hrefeq heq.symm)
      exact ⟨h2, hsub1.trans hsub2⟩
  intro commentRef hmem
  rw [Std.HashMap.mem_keys, Std.HashMap.mem_insert, Std.HashMap.mem_insert] at hmem
  rcases hmem with hpeq | hceq | hold
  · have hpeq' : parentThreadRef = commentRef := beq_iff_eq.mp hpeq
    subst hpeq'
    obtain ⟨loc', threadsList', hpair, root, hrootmem, hreach⟩ :=
      commentThreads.hAllCommentTreeNodesAreLive parentThreadRef (Std.HashMap.mem_keys.mpr hMemTree)
    exact ⟨loc', threadsList', hpair, root, hrootmem, NodeReachable_mono hMonoOldToFinal hreach⟩
  · have hceq' : ref = commentRef := beq_iff_eq.mp hceq
    subst hceq'
    obtain ⟨loc', threadsList', hpair, root, hrootmem, hreachParent⟩ :=
      commentThreads.hAllCommentTreeNodesAreLive parentThreadRef (Std.HashMap.mem_keys.mpr hMemTree)
    have hreachParentFinal := NodeReachable_mono hMonoOldToFinal hreachParent
    have hfmem : parentThreadRef ∈ treeNodesWithThis.insert parentThreadRef updatedParentThread :=
      Std.HashMap.mem_insert_self
    have hchildmem : ref ∈ ((treeNodesWithThis.insert parentThreadRef updatedParentThread).get
        parentThreadRef hfmem).children := by
      have hget : (treeNodesWithThis.insert parentThreadRef updatedParentThread).get parentThreadRef hfmem =
          updatedParentThread := by
        show (treeNodesWithThis.insert parentThreadRef updatedParentThread)[parentThreadRef]'hfmem =
          updatedParentThread
        exact Std.HashMap.getElem_insert_self
      rw [hget, hUpdatedChildren]
      exact List.mem_cons_self
    exact ⟨loc', threadsList', hpair, root, hrootmem,
      CommentThreads.NodeReachable.step hreachParentFinal hfmem hchildmem⟩
  · obtain ⟨loc', threadsList', hpair, root, hrootmem, hreach⟩ :=
      commentThreads.hAllCommentTreeNodesAreLive commentRef (Std.HashMap.mem_keys.mpr hold)
    exact ⟨loc', threadsList', hpair, root, hrootmem, NodeReachable_mono hMonoOldToFinal hreach⟩

public def addCommentToThread (commentThreads : CommentThreads) (comment : Comment) (hHasBackendId : comment.backendId.isSome)
    (hParentValid : ∀ parentId, comment.parent = some parentId → parentId ∈ commentThreads.serverCommentIds)
    (hParentThreadRegistered : ∀ parentId (h : parentId ∈ commentThreads.serverCommentIds),
      comment.parent = some parentId → commentThreads.serverCommentIds.get parentId h ∈ commentThreads.commentTreeNodes)
    (hRefFresh : comment.ref ∉ commentThreads.commentTreeNodes)
    (hLocationScope : ∀ loc', loc' ∈ commentThreads.locationRoots.keys →
      loc'.isTopLevel = comment.location.asThreadLocation.isTopLevel) :
    CommentThreads :=
  let treeNode := ⟨comment.ref, []⟩
  let treeNodesWithThis := commentThreads.commentTreeNodes.insert comment.ref treeNode
  let loc := comment.location.asThreadLocation

  -- If the location is empty, just add this as a top-level thread
  --
  -- Otherwise, find the thread of the parent and add this as a child
  match hEq : comment.parent with
  | some parentServerId =>
    let hMemServer := hParentValid parentServerId hEq
    let parentThreadRef := commentThreads.serverCommentIds.get parentServerId hMemServer
    let hMemTree := hParentThreadRegistered parentServerId hMemServer hEq
    let parentThread := commentThreads.commentTreeNodes.get parentThreadRef hMemTree
    let updatedParentThread := ⟨parentThread.value, comment.ref :: parentThread.children⟩
    { commentTreeNodes := treeNodesWithThis.insert parentThreadRef updatedParentThread,
      serverCommentIds := commentThreads.serverCommentIds.insert (comment.backendId.get hHasBackendId) comment.ref,
      locationRoots := commentThreads.locationRoots,
      hLocationsConsistent := commentThreads.hLocationsConsistent,
      hHasNodeForComment := fun loc' threadRoots' hpair ref' href' =>
        contains_mono_insert treeNodesWithThis parentThreadRef updatedParentThread ref'
          (contains_mono_insert commentThreads.commentTreeNodes comment.ref treeNode ref'
            (commentThreads.hHasNodeForComment loc' threadRoots' hpair ref' href')),
      hAllCommentTreeNodesAreLive := hAllCommentTreeNodesAreLive_insert_reply commentThreads comment.ref treeNode
        parentThreadRef hMemTree updatedParentThread rfl hRefFresh,
      hCommentTreeNodeRootMatchesKey := hCommentTreeNodeRootMatchesKey_insert treeNodesWithThis parentThreadRef
        updatedParentThread (commentThreads.hCommentTreeNodeRootMatchesKey parentThreadRef hMemTree)
        (hCommentTreeNodeRootMatchesKey_insert commentThreads.commentTreeNodes comment.ref treeNode rfl
          commentThreads.hCommentTreeNodeRootMatchesKey),
      hLocationRootsNodup := commentThreads.hLocationRootsNodup,
      hChildrenAreRegistered := hChildrenAreRegistered_insert treeNodesWithThis parentThreadRef updatedParentThread
        (fun child hc => by
          rcases List.mem_cons.mp hc with heq | hold
          · rw [heq]
            exact contains_mono_insert treeNodesWithThis parentThreadRef updatedParentThread comment.ref
              Std.HashMap.contains_insert_self
          · exact contains_mono_insert treeNodesWithThis parentThreadRef updatedParentThread child
              (contains_mono_insert commentThreads.commentTreeNodes comment.ref treeNode child
                (commentThreads.hChildrenAreRegistered parentThreadRef hMemTree child hold)))
        (hChildrenAreRegistered_insert commentThreads.commentTreeNodes comment.ref treeNode
          (fun child hc => absurd hc List.not_mem_nil)
          commentThreads.hChildrenAreRegistered),
      hServerCommentIdsRegistered := fun sid h => by
        by_cases heq : (comment.backendId.get hHasBackendId) == sid
        · have hkey : comment.backendId.get hHasBackendId = sid := beq_iff_eq.mp heq
          subst hkey
          rw [Std.HashMap.get_insert_self]
          exact contains_mono_insert treeNodesWithThis parentThreadRef updatedParentThread comment.ref
            Std.HashMap.contains_insert_self
        · have hOld : commentThreads.serverCommentIds.contains sid := by
            have h' := h
            rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at h'
            rcases h' with h1 | h1
            · exact absurd (beq_iff_eq.mpr h1) heq
            · exact h1
          rw [Std.HashMap.get_insert_of_ne heq h hOld]
          exact contains_mono_insert treeNodesWithThis parentThreadRef updatedParentThread
            (commentThreads.serverCommentIds.get sid hOld)
            (contains_mono_insert commentThreads.commentTreeNodes comment.ref treeNode
              (commentThreads.serverCommentIds.get sid hOld)
              (commentThreads.hServerCommentIdsRegistered sid hOld))
    }
  | none =>
    { commentTreeNodes := treeNodesWithThis,
      serverCommentIds := commentThreads.serverCommentIds.insert (comment.backendId.get hHasBackendId) comment.ref,
      locationRoots := commentThreads.locationRoots.alter loc (insertSingletonOrAppend comment.ref),
      hLocationsConsistent := hLocationsConsistent_alter commentThreads.locationRoots loc comment.ref
        commentThreads.hLocationsConsistent hLocationScope,
      hHasNodeForComment := hHasNodeForComment_alter commentThreads.locationRoots commentThreads.commentTreeNodes
        treeNodesWithThis loc comment.ref commentThreads.hHasNodeForComment
        (contains_mono_insert commentThreads.commentTreeNodes comment.ref treeNode)
        Std.HashMap.contains_insert_self,
      hAllCommentTreeNodesAreLive :=
        hAllCommentTreeNodesAreLive_alter commentThreads comment.ref treeNode loc hRefFresh,
      hCommentTreeNodeRootMatchesKey := hCommentTreeNodeRootMatchesKey_insert commentThreads.commentTreeNodes
        comment.ref treeNode rfl commentThreads.hCommentTreeNodeRootMatchesKey,
      hLocationRootsNodup := hLocationRootsNodup_alter commentThreads.locationRoots commentThreads.commentTreeNodes
        loc comment.ref commentThreads.hHasNodeForComment hRefFresh commentThreads.hLocationRootsNodup,
      hChildrenAreRegistered := hChildrenAreRegistered_insert commentThreads.commentTreeNodes comment.ref treeNode
        (fun child hc => absurd hc List.not_mem_nil)
        commentThreads.hChildrenAreRegistered,
      hServerCommentIdsRegistered := fun sid h => by
        by_cases heq : (comment.backendId.get hHasBackendId) == sid
        · have hkey : comment.backendId.get hHasBackendId = sid := beq_iff_eq.mp heq
          subst hkey
          rw [Std.HashMap.get_insert_self]
          exact Std.HashMap.contains_insert_self
        · have hOld : commentThreads.serverCommentIds.contains sid := by
            have h' := h
            rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at h'
            rcases h' with h1 | h1
            · exact absurd (beq_iff_eq.mpr h1) heq
            · exact h1
          rw [Std.HashMap.get_insert_of_ne heq h hOld]
          exact contains_mono_insert commentThreads.commentTreeNodes comment.ref treeNode
            (commentThreads.serverCommentIds.get sid hOld) (commentThreads.hServerCommentIdsRegistered sid hOld)
    }

/-- If every existing location key in `commentThreads` agrees with `comment`'s own location on
top-level-ness (`b`), then every location key `addCommentToThread` produces agrees too. Used by
`completeCommentWithContent` to re-establish `CommentManager.hTopLevelThreadsAllTopLevel` (`b :=
true`) after publishing a new top-level comment, and `ModifiedFileState.hBaseThreadsFileScoped` /
`hCurrentThreadsFileScoped` (`b := false`) after publishing a new file-scoped comment: the
`some`-parent branch leaves `locationRoots` untouched, and the `none`-parent branch only ever adds
`comment.location.asThreadLocation` (which already agrees with `b`) as a new key. -/
public theorem addCommentToThread_locationRoots_isTopLevel
    (commentThreads : CommentThreads) (comment : Comment) (hHasBackendId : comment.backendId.isSome)
    (hParentValid : ∀ parentId, comment.parent = some parentId → parentId ∈ commentThreads.serverCommentIds)
    (hParentThreadRegistered : ∀ parentId (h : parentId ∈ commentThreads.serverCommentIds),
      comment.parent = some parentId →
        commentThreads.serverCommentIds.get parentId h ∈ commentThreads.commentTreeNodes)
    (hRefFresh : comment.ref ∉ commentThreads.commentTreeNodes)
    (hLocationScope : ∀ loc', loc' ∈ commentThreads.locationRoots.keys →
      loc'.isTopLevel = comment.location.asThreadLocation.isTopLevel)
    (b : Bool)
    (hOldAllB : ∀ loc, loc ∈ commentThreads.locationRoots.keys → loc.isTopLevel = b)
    (hCommentB : comment.location.asThreadLocation.isTopLevel = b) :
    ∀ loc', loc' ∈ (addCommentToThread commentThreads comment hHasBackendId hParentValid
        hParentThreadRegistered hRefFresh hLocationScope).locationRoots.keys → loc'.isTopLevel = b := by
  intro loc' hloc'
  unfold addCommentToThread at hloc'
  split at hloc'
  · exact hOldAllB loc' hloc'
  · rw [Std.HashMap.mem_keys, mem_alter_insertSingletonOrAppend] at hloc'
    rcases hloc' with heq | hold
    · exact heq ▸ hCommentB
    · exact hOldAllB loc' (Std.HashMap.mem_keys.mpr hold)

/-- `addCommentToThread` registers exactly one new tree-node key: `comment.ref`. Used by
`completeCommentWithContent` to re-establish `CommentManager.hTopLevelThreadsPublished` after
publishing a new top-level comment. -/
public theorem addCommentToThread_commentTreeNodes_contains_iff
    (commentThreads : CommentThreads) (comment : Comment) (hHasBackendId : comment.backendId.isSome)
    (hParentValid : ∀ parentId, comment.parent = some parentId → parentId ∈ commentThreads.serverCommentIds)
    (hParentThreadRegistered : ∀ parentId (h : parentId ∈ commentThreads.serverCommentIds),
      comment.parent = some parentId →
        commentThreads.serverCommentIds.get parentId h ∈ commentThreads.commentTreeNodes)
    (hRefFresh : comment.ref ∉ commentThreads.commentTreeNodes)
    (hLocationScope : ∀ loc', loc' ∈ commentThreads.locationRoots.keys →
      loc'.isTopLevel = comment.location.asThreadLocation.isTopLevel) (ref' : CommentRef) :
    (addCommentToThread commentThreads comment hHasBackendId hParentValid hParentThreadRegistered
        hRefFresh hLocationScope).commentTreeNodes.contains ref' ↔
      commentThreads.commentTreeNodes.contains ref' ∨ ref' = comment.ref := by
  unfold addCommentToThread
  split
  · dsimp only
    simp only [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq]
    rename_i parentServerId hEq
    have hMemServer := hParentValid parentServerId hEq
    have hMemTree := hParentThreadRegistered parentServerId hMemServer hEq
    constructor
    · rintro (h | h | h)
      · exact Or.inl (h ▸ Std.HashMap.mem_iff_contains.mp hMemTree)
      · exact Or.inr h.symm
      · exact Or.inl h
    · rintro (h | h)
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h.symm)
  · dsimp only
    simp only [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq]
    constructor
    · rintro (h | h)
      · exact Or.inr h.symm
      · exact Or.inl h
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl h.symm

/-- `addCommentToThread` always registers the newly-published comment's backend id, mapped to its
own ref, into `serverCommentIds` — identically in both branches. Used by
`completeCommentWithContent` to re-establish `CommentManager.hServerCommentIdsRegistered`. -/
public theorem addCommentToThread_serverCommentIds_eq
    (commentThreads : CommentThreads) (comment : Comment) (hHasBackendId : comment.backendId.isSome)
    (hParentValid : ∀ parentId, comment.parent = some parentId → parentId ∈ commentThreads.serverCommentIds)
    (hParentThreadRegistered : ∀ parentId (h : parentId ∈ commentThreads.serverCommentIds),
      comment.parent = some parentId →
        commentThreads.serverCommentIds.get parentId h ∈ commentThreads.commentTreeNodes)
    (hRefFresh : comment.ref ∉ commentThreads.commentTreeNodes)
    (hLocationScope : ∀ loc', loc' ∈ commentThreads.locationRoots.keys →
      loc'.isTopLevel = comment.location.asThreadLocation.isTopLevel) :
    (addCommentToThread commentThreads comment hHasBackendId hParentValid hParentThreadRegistered
        hRefFresh hLocationScope).serverCommentIds =
      commentThreads.serverCommentIds.insert (comment.backendId.get hHasBackendId) comment.ref := by
  unfold addCommentToThread
  split <;> rfl

/-- Publishing `comment` (fresh at `ref`, per `addCommentToThread`'s hypotheses) preserves
`CommentManager.hTopLevelThreadsPublished`: every tree node in the resulting `topLevelThreads` is
still backed by a published comment -- either it was already published (delegating to the old
invariant, since inserting `comment` at the fresh `ref` doesn't disturb any other key) or it's
`comment` itself, now published via `hHasBackendId`. -/
public theorem CommentManager.hTopLevelThreadsPublished_insert (manager : CommentManager) (ref : CommentRef)
    (comment : Comment) (href : comment.ref = ref) (hHasBackendId : comment.backendId.isSome)
    (hParentValid : ∀ parentId, comment.parent = some parentId → parentId ∈ manager.topLevelThreads.serverCommentIds)
    (hParentThreadRegistered : ∀ parentId (h : parentId ∈ manager.topLevelThreads.serverCommentIds),
      comment.parent = some parentId →
        manager.topLevelThreads.serverCommentIds.get parentId h ∈ manager.topLevelThreads.commentTreeNodes)
    (hRefFresh : comment.ref ∉ manager.topLevelThreads.commentTreeNodes)
    (hLocationScope : ∀ loc', loc' ∈ manager.topLevelThreads.locationRoots.keys →
      loc'.isTopLevel = comment.location.asThreadLocation.isTopLevel) :
    ∀ ref' (_h : (addCommentToThread manager.topLevelThreads comment hHasBackendId hParentValid
        hParentThreadRegistered hRefFresh hLocationScope).commentTreeNodes.contains ref'),
      ∃ h' : (manager.comments.insert ref comment).contains ref',
        ((manager.comments.insert ref comment).get ref' h').backendId.isSome := by
  intro ref' h
  rw [addCommentToThread_commentTreeNodes_contains_iff manager.topLevelThreads comment
    hHasBackendId hParentValid hParentThreadRegistered hRefFresh hLocationScope] at h
  rcases h with hold | hnew
  · obtain ⟨hExists'', hSome⟩ := manager.hTopLevelThreadsPublished ref' hold
    have hne : ¬ (ref == ref') := by
      simp only [beq_iff_eq]
      intro heq
      rw [← heq] at hold
      exact hRefFresh (href ▸ Std.HashMap.mem_iff_contains.mpr hold)
    have hc : (manager.comments.insert ref comment).contains ref' := by
      rw [Std.HashMap.contains_insert, Bool.or_eq_true]; exact Or.inr hExists''
    refine ⟨hc, ?_⟩
    rw [Std.HashMap.get_insert_of_ne hne hc hExists'']; exact hSome
  · have hnew' : ref = ref' := href.symm.trans hnew.symm
    subst hnew'
    have hc : (manager.comments.insert ref comment).contains ref := Std.HashMap.contains_insert_self
    refine ⟨hc, ?_⟩
    rw [Std.HashMap.get_insert_self hc]
    exact hHasBackendId

