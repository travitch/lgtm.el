module

import Std

import all LgtmLean.Basic
import all LgtmLean.Tree

def commentsAllInSameFileOrAllTopLevel (comments : List Comment) : Prop :=
  (∀ c, c ∈ comments → c.location.isTopLevel) ∨
  (∀ c, c ∈ comments → ∃ loc, c.location = .fileLocation loc ∧ loc.version = .base) ∨
  (∀ c, c ∈ comments → ∃ loc, c.location = .fileLocation loc ∧ loc.version = .current)

def allCommentsHaveBackendId (comments : List Comment) : Prop := ∀ c, c ∈ comments → c.backendId.isSome

/-- Every parent referenced by a comment in the batch is itself the backend id of some comment in
the batch.  This is needed to look the parent up in `serverCommentIds` while assembling threads. -/
def allParentsInComments (comments : List Comment) : Prop :=
  ∀ c, c ∈ comments → ∀ parentId, c.parent = some parentId → ∃ c', c' ∈ comments ∧ c'.backendId = some parentId

private structure CommentTreeBootstrapState where
  commentTreeNodes : Std.HashMap CommentRef CommentThread
  serverCommentIds : Std.HashMap ServerId CommentRef
  locationRoots : Std.HashMap ThreadLocation (List CommentRef)

private def emptyBootstrapState : CommentTreeBootstrapState := ⟨Std.HashMap.emptyWithCapacity, Std.HashMap.emptyWithCapacity, Std.HashMap.emptyWithCapacity⟩

private def insertSingletonOrAppend (value : α) (current : Option (List α)) : Option (List α) :=
  match current with
  | none => some [value]
  | some values => some (value :: values)

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

/-- Attach every reply comment to its parent's tree node, and collect the root comments into
`locationRoots`.  Written as a pure fold over `comments` (rather than a monadic `for` loop) so that
the invariant `hInv` -- every parent id we might look up already has a live node in
`commentTreeNodes` -- can be threaded explicitly through the recursion and re-established at each
step, instead of needing to be re-derived from an opaque, progressively-mutated `StateT` state. -/
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
                         : CommentThreads :=
  let finalState := bootstrapCommentTrees comments hCommentsHaveBackendIds hParentsInComments
    emptyBootstrapState (fun sid h => absurd h Std.HashMap.not_mem_emptyWithCapacity)
  { commentTreeNodes := finalState.commentTreeNodes,
    serverCommentIds := finalState.serverCommentIds,
    locationRoots := finalState.locationRoots,
    hLocationsConsistent := sorry,
    hHasNodeForComment := sorry,
    hAllCommentTreeNodesAreLive := sorry,
    hCommentTreeNodeRootMatchesKey := sorry,
    hLocationRootsNodup := sorry
    }
