module

import Std

public import LgtmLean.Basic
public import LgtmLean.CreateThreads


/-- Delete all of the comments in the current review state.

This is used to prepare to fetch an updated state from the server. -/
public def resetCommentState : LgtmM Unit := do
  let s₀ ← get
  let manager₁ := s₀.fileManager.resetCommentState
  set { s₀ with commentBeingEdited := none, commentManager := CommentManager.empty, fileManager := manager₁, hCommentBeingEditedWellFormed := by simp }


public def addRemoteComments (comments : List Comment) : LgtmM Unit := do
  pure ()

/-- The core worker called to update the state when the user marks a comment as done.

Returns the finalized comment so that the interactive wrapper can make relevant UI updates (e.g.,
updating overlays).



This fails (returns no comment and updates no state) if:

1) There was no comment being updated,
2) The string was empty, or
3) Calling the server store function fails

Note that we could add a proof obligation that the content is not empty, but this is called from a
context outside of the context of the Lean code, so that proof obligation cannot be fulfilled.

-/
public def completeCommentWithContent (newContent : String) : LgtmM Comment := do
  if newContent.isEmpty then
    throw "Comments cannot be empty"

  let s₀ ← StateT.get
  match hBeingEdited : s₀.commentBeingEdited with
  | none => throw "No active comment"
  | some editedCommentRef =>
    let comment₀ := s₀.commentManager.get editedCommentRef
    let comment₁ := { comment₀ with content := newContent }
    match s₀.configuration.createComment comment₁ with
    | none => throw "Failed to create the comment on the server"
    | some serverId =>
      let comment₂ := { comment₁ with backendId := serverId }

      have hDerived := s₀.commentManager.get_of_commentBeingEditedWellFormed editedCommentRef
        (s₀.hCommentBeingEditedWellFormed editedCommentRef hBeingEdited)
      have href0 : comment₀.ref = editedCommentRef := hDerived.1
      have hbid0 : comment₀.backendId = none := hDerived.2.1
      have hparent0 : ∀ parentId, comment₀.parent = some parentId →
          parentId ∈ s₀.commentManager.topLevelThreads.serverCommentIds := hDerived.2.2

      match hloc : comment₂.location with
      | .topLevel =>
        have href2 : comment₂.ref = editedCommentRef := href0
        have hparent2 : ∀ parentId, comment₂.parent = some parentId →
            parentId ∈ s₀.commentManager.topLevelThreads.serverCommentIds := hparent0
        have hbackendId2 : comment₂.backendId = some serverId := rfl
        have hHasBackendId : comment₂.backendId.isSome := by rw [hbackendId2]; rfl

        have hParentThreadRegistered : ∀ parentId (h : parentId ∈ s₀.commentManager.topLevelThreads.serverCommentIds),
            comment₂.parent = some parentId →
              s₀.commentManager.topLevelThreads.serverCommentIds.get parentId h ∈
                s₀.commentManager.topLevelThreads.commentTreeNodes :=
          fun parentId h _ => s₀.commentManager.hParentThreadRegistered_mem parentId h

        have hRefFresh : ¬ comment₂.ref ∈ s₀.commentManager.topLevelThreads.commentTreeNodes := by
          rw [href2]
          exact s₀.commentManager.notMem_topLevelThreads_of_unpublished editedCommentRef hbid0

        have hLocationScope : ∀ loc', loc' ∈ s₀.commentManager.topLevelThreads.locationRoots.keys →
            loc'.isTopLevel = comment₂.location.asThreadLocation.isTopLevel :=
          s₀.commentManager.locationScope_of_topLevel hloc

        let topLevelThreads₁ := addCommentToThread s₀.commentManager.topLevelThreads comment₂
          hHasBackendId hparent2 hParentThreadRegistered hRefFresh hLocationScope

        let comments₁ := s₀.commentManager.comments.insert editedCommentRef comment₂

        have hCommentsKeyedByRef₁ : ∀ ref (h : comments₁.contains ref), (comments₁.get ref h).ref = ref :=
          s₀.commentManager.hCommentsKeyedByRef_insert editedCommentRef comment₂ href2

        have hTopLevelThreadsAllTopLevel₁ : ∀ loc', loc' ∈ topLevelThreads₁.locationRoots.keys →
            loc'.isTopLevel = true :=
          addCommentToThread_locationRoots_isTopLevel s₀.commentManager.topLevelThreads comment₂
            hHasBackendId hparent2 hParentThreadRegistered hRefFresh hLocationScope
            s₀.commentManager.hTopLevelThreadsAllTopLevel
            (hloc ▸ CommentLocation.topLevel_asThreadLocation_isTopLevel)

        have hTopLevelThreadsPublished₁ : ∀ ref' (h : topLevelThreads₁.commentTreeNodes.contains ref'),
            ∃ h' : comments₁.contains ref', (comments₁.get ref' h').backendId.isSome :=
          s₀.commentManager.hTopLevelThreadsPublished_insert editedCommentRef comment₂ href2
            hHasBackendId hparent2 hParentThreadRegistered hRefFresh hLocationScope

        have hServerCommentIdsRegistered₁ : ∀ sid (h : topLevelThreads₁.serverCommentIds.contains sid),
            topLevelThreads₁.commentTreeNodes.contains (topLevelThreads₁.serverCommentIds.get sid h) :=
          s₀.commentManager.hServerCommentIdsRegistered_insert comment₂
            hHasBackendId hparent2 hParentThreadRegistered hRefFresh hLocationScope

        let commentManager₁ : CommentManager :=
          { comments := comments₁,
            topLevelThreads := topLevelThreads₁,
            selectedComment := none,
            hSelectedCommentWellFormed := by simp,
            hCommentsKeyedByRef := hCommentsKeyedByRef₁,
            hTopLevelThreadsAllTopLevel := hTopLevelThreadsAllTopLevel₁,
            hTopLevelThreadsPublished := hTopLevelThreadsPublished₁,
            hServerCommentIdsRegistered := hServerCommentIdsRegistered₁ }
        StateT.set { s₀ with commentBeingEdited := none, commentManager := commentManager₁, hCommentBeingEditedWellFormed := by simp }
      | .fileLocation loc => pure ()


      pure comment₂
