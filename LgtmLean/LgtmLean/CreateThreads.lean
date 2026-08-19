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

private abbrev BootstrapM α := StateM CommentTreeBootstrapState α

private def registerServerCommentIds (comments : List Comment)
                                     (hCommentsHaveBackendIds : allCommentsHaveBackendId comments)
                                     : BootstrapM Unit := do
  for h : comment in comments do
    let treeNode : CommentThread := ⟨comment.ref, []⟩
    let serverId := comment.backendId.get (hCommentsHaveBackendIds comment h)
    StateT.modifyGet (λ s => ((), {s with commentTreeNodes := s.commentTreeNodes.insert comment.ref treeNode,
                                          serverCommentIds := s.serverCommentIds.insert serverId comment.ref
                              }))

private theorem registerServerCommentIds_cons
    (head : Comment) (tail : List Comment) (hAll : allCommentsHaveBackendId (head :: tail))
    (s₀ : CommentTreeBootstrapState) :
    (registerServerCommentIds (head :: tail) hAll).run s₀ =
      (registerServerCommentIds tail (fun c hc => hAll c (List.mem_cons_of_mem head hc))).run
        { s₀ with commentTreeNodes := s₀.commentTreeNodes.insert head.ref ⟨head.ref, []⟩,
                  serverCommentIds := s₀.serverCommentIds.insert
                    (head.backendId.get (hAll head List.mem_cons_self)) head.ref } := by
  simp only [registerServerCommentIds, List.forIn'_cons, StateT.run, bind, StateT.bind, pure,
    StateT.pure, StateT.modifyGet]

private theorem serverCommentIds_contains_of_contains
    (comments : List Comment) (hAll : allCommentsHaveBackendId comments)
    (s₀ : CommentTreeBootstrapState) (sid : ServerId) (h₀ : s₀.serverCommentIds.contains sid) :
    ((registerServerCommentIds comments hAll).run s₀).snd.serverCommentIds.contains sid := by
  induction comments generalizing s₀ with
  | nil => simpa [registerServerCommentIds, StateT.run, StateT.pure, StateT.bind, bind, pure] using h₀
  | cons head tail ih =>
    rw [registerServerCommentIds_cons]
    apply ih
    exact Std.HashMap.mem_insert.mpr (Or.inr h₀)

private theorem serverCommentIds_contains_of_mem
    (comments : List Comment) (hCommentsHaveBackendIds : allCommentsHaveBackendId comments)
    (s₀ : CommentTreeBootstrapState) (c : Comment) (hc : c ∈ comments) (sid : ServerId)
    (hsid : c.backendId = some sid) :
    ((registerServerCommentIds comments hCommentsHaveBackendIds).run s₀).snd.serverCommentIds.contains sid := by
  induction comments generalizing s₀ with
  | nil => cases hc
  | cons head tail ih =>
    rw [registerServerCommentIds_cons]
    rcases List.mem_cons.mp hc with rfl | hc'
    · apply serverCommentIds_contains_of_contains
      simp only [hsid, Option.get_some]
      exact Std.HashMap.mem_insert_self
    · exact ih _ _ hc'

private def bootstrapCommentTrees (comments : List Comment)
                                  (hSameLocation : commentsAllInSameFileOrAllTopLevel comments)
                                  (hCommentsHaveBackendIds : allCommentsHaveBackendId comments)
                                  (hParentsInComments : allParentsInComments comments)
                                  : BootstrapM Unit := do
  let s₀ ← StateT.get
  let s₁ := ((registerServerCommentIds comments hCommentsHaveBackendIds).run s₀).snd
  StateT.set s₁
  let serverCommentIds := s₁.serverCommentIds

  for h1 : comment in comments do
    let treeNode := (← StateT.get).commentTreeNodes.get comment.ref
    let locationKey := comment.location.asThreadLocation
    match h2 : comment.parent with
    | none => do
      -- This is a root comment
      StateT.modifyGet (λ s => ((), {s with locationRoots := s.locationRoots.alter locationKey (insertSingletonOrAppend comment.ref)}))
    | some parentId => do
      -- This is a comment inside of a thread
      have hContainsParentId : serverCommentIds.contains parentId := by
        obtain ⟨c', hc', hc'sid⟩ := hParentsInComments comment h1 parentId h2
        exact serverCommentIds_contains_of_mem comments hCommentsHaveBackendIds s₀ c' hc' parentId hc'sid
      let parentNodeRef := serverCommentIds.get parentId hContainsParentId
      let parentTreeNode := (← StateT.get).commentTreeNodes.get parentNodeRef sorry
      StateT.modifyGet (λ s => ((), {s with commentTreeNodes := s.commentTreeNodes.insert parentNodeRef (parentTreeNode.addChild comment.ref) }))

  pure ()

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
  let (_, finalState) := StateT.run (bootstrapCommentTrees comments hSameLocation hCommentsHaveBackendIds hParentsInComments) emptyBootstrapState
  { commentTreeNodes := finalState.commentTreeNodes,
    serverCommentIds := finalState.serverCommentIds,
    locationRoots := finalState.locationRoots,
    hLocationsConsistent := sorry,
    hHasNodeForComment := sorry,
    hAllCommentTreeNodesAreLive := sorry,
    hCommentTreeNodeRootMatchesKey := sorry,
    hLocationRootsNodup := sorry
    }
