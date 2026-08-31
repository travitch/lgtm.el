module

import Std

public import LgtmLean.Basic
public import LgtmLean.CreateThreads

public structure Result α where
  value : α
  updatedState : State

/-- Delete all of the comments in the current review state.

This is used to prepare to fetch an updated state from the server. -/
public def resetCommentState (s₀ : State) : Result Unit :=
  let manager₁ := s₀.fileManager.resetCommentState
  let s₁ := { s₀ with
              commentBeingEdited := none,
              commentManager := CommentManager.empty,
              fileManager := manager₁,
              hCommentBeingEditedWellFormed := by simp,
              hFileThreadsPublished := s₀.fileManager.hFileThreadsPublished_resetCommentState CommentManager.empty.comments }
  Result.mk () s₁


public def addRemoteComments (s₀ : State) (comments : List Comment) : Result Unit := sorry

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
public def completeCommentWithContent (s₀ : State) (newContent : String) : Result (Except String Comment) :=
  if newContent.isEmpty then
    Result.mk (Except.error "Comments cannot be empty") s₀
  else
    match hBeingEdited : s₀.commentBeingEdited with
    | none => Result.mk (Except.error "No active comment") s₀
    | some editedCommentRef =>
      let comment₀ := s₀.commentManager.get editedCommentRef
      let comment₁ := { comment₀ with content := newContent }
      match s₀.configuration.createComment comment₁ with
      | none => Result.mk (Except.error "Failed to create the comment on the server") s₀
      | some serverId =>
        let comment₂ : Comment := { comment₁ with backendId := serverId }
        have hbackendId2 : comment₂.backendId = some serverId := rfl
        have hHasBackendId : comment₂.backendId.isSome := by rw [hbackendId2]; rfl

        have hDerived := s₀.commentManager.get_of_commentBeingEditedWellFormed s₀.fileManager editedCommentRef
          (s₀.hCommentBeingEditedWellFormed editedCommentRef hBeingEdited)
        have href0 : comment₀.ref = editedCommentRef := hDerived.1
        have hbid0 : comment₀.backendId = none := hDerived.2.1
        have hparent0 := hDerived.2.2

        have href2 : comment₂.ref = editedCommentRef := href0

        let comments₁ := s₀.commentManager.comments.insert editedCommentRef comment₂

        have hCommentsKeyedByRef₁ : ∀ ref (h : comments₁.contains ref), (comments₁.get ref h).ref = ref :=
          s₀.commentManager.hCommentsKeyedByRef_insert editedCommentRef comment₂ href2

        -- Inserting the (freshly-published) being-edited comment into `comments` can't disturb any
        -- other ref's published status: it either was already there and is untouched, or it *is*
        -- `editedCommentRef`, which was unpublished (`hbid0`) and so can't have been the ref some
        -- other invariant already certified as published.
        have hPreservePublished := s₀.commentManager.preservePublished_insert hbid0 comment₂

        have hFileThreadsPublished₁ : ∀ modifiedFileRef (h : s₀.fileManager.state.contains modifiedFileRef),
            (∀ ref (hc : (s₀.fileManager.state.get modifiedFileRef h).baseThreads.commentTreeNodes.contains ref),
              ∃ h' : comments₁.contains ref, (comments₁.get ref h').backendId.isSome) ∧
            (∀ ref (hc : (s₀.fileManager.state.get modifiedFileRef h).currentThreads.commentTreeNodes.contains ref),
              ∃ h' : comments₁.contains ref, (comments₁.get ref h').backendId.isSome) := by
          intro modifiedFileRef h
          obtain ⟨hBase, hCurrent⟩ := s₀.hFileThreadsPublished modifiedFileRef h
          refine ⟨fun ref hc => ?_, fun ref hc => ?_⟩
          · obtain ⟨h', hpub'⟩ := hBase ref hc
            exact hPreservePublished ref h' hpub'
          · obtain ⟨h', hpub'⟩ := hCurrent ref hc
            exact hPreservePublished ref h' hpub'

        match hloc : comment₀.location with
        | .topLevel =>
          have hparent2 : ∀ parentId, comment₂.parent = some parentId →
              parentId ∈ s₀.commentManager.topLevelThreads.serverCommentIds := by
            intro parentId hp
            have hres := hparent0 parentId hp
            rw [hloc] at hres
            exact hres

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

          have hTopLevelThreadsAllTopLevel₁ : ∀ loc', loc' ∈ topLevelThreads₁.locationRoots.keys →
              loc'.isTopLevel = true :=
            addCommentToThread_locationRoots_isTopLevel s₀.commentManager.topLevelThreads comment₂
              hHasBackendId hparent2 hParentThreadRegistered hRefFresh hLocationScope true
              s₀.commentManager.hTopLevelThreadsAllTopLevel
              (hloc ▸ CommentLocation.topLevel_asThreadLocation_isTopLevel)

          have hTopLevelThreadsPublished₁ : ∀ ref' (h : topLevelThreads₁.commentTreeNodes.contains ref'),
              ∃ h' : comments₁.contains ref', (comments₁.get ref' h').backendId.isSome :=
            s₀.commentManager.hTopLevelThreadsPublished_insert editedCommentRef comment₂ href2
              hHasBackendId hparent2 hParentThreadRegistered hRefFresh hLocationScope

          let commentManager₁ : CommentManager :=
            { comments := comments₁,
              topLevelThreads := topLevelThreads₁,
              selectedComment := none,
              hSelectedCommentWellFormed := by simp,
              hCommentsKeyedByRef := hCommentsKeyedByRef₁,
              hTopLevelThreadsAllTopLevel := hTopLevelThreadsAllTopLevel₁,
              hTopLevelThreadsPublished := hTopLevelThreadsPublished₁ }
          let s₁ := { s₀ with
                      commentBeingEdited := none,
                      commentManager := commentManager₁,
                      hCommentBeingEditedWellFormed := by simp,
                      hFileThreadsPublished := hFileThreadsPublished₁ }
          Result.mk (Except.ok comment₂) s₁
        | .fileLocation loc =>
          match hfound : s₀.fileManager.state.toList.find? (λ (_, modifiedFileState) => modifiedFileState.fileRef == loc.fileRef) with
          | none => Result.mk (Except.error "Unexpected file") s₀
          | some (fileRef, modifiedFileState) =>
            have hFound := s₀.fileManager.contains_get_of_find? hfound
            have hOldContainsFileRef := hFound.1
            have hgetval := hFound.2.1
            have hpred := hFound.2.2
            have hmem : (fileRef, modifiedFileState) ∈ s₀.fileManager.state.toList := List.mem_of_find?_eq_some hfound

            have hOldPublishedFile := hgetval ▸ s₀.hFileThreadsPublished fileRef hOldContainsFileRef

            -- `topLevelThreads` is untouched by a file-scoped comment; only `comments` grows.
            have hTopLevelThreadsPublished₁ := s₀.commentManager.hTopLevelThreadsPublished_of_preserve hPreservePublished

            have hparentFile : ∀ parentId, comment₂.parent = some parentId →
                parentId ∈ (match loc.version with
                  | .base => modifiedFileState.baseThreads
                  | .current => modifiedFileState.currentThreads).serverCommentIds := by
              intro parentId hp
              have hp0 := hparent0 parentId hp
              rw [hloc] at hp0
              exact hp0 fileRef modifiedFileState hmem hpred

            have hcommentTop : comment₂.location.asThreadLocation.isTopLevel = false :=
              hloc ▸ CommentLocation.fileLocation_asThreadLocation_isTopLevel loc

            have hRefFreshBase : comment₂.ref ∉ modifiedFileState.baseThreads.commentTreeNodes := by
              rw [href2, ← hgetval]
              exact s₀.notMem_baseThreads_of_unpublished hbid0 hOldContainsFileRef

            have hRefFreshCurrent : comment₂.ref ∉ modifiedFileState.currentThreads.commentTreeNodes := by
              rw [href2, ← hgetval]
              exact s₀.notMem_currentThreads_of_unpublished hbid0 hOldContainsFileRef

            have hLocationScopeBase := modifiedFileState.locationScope_of_base hcommentTop
            have hLocationScopeCurrent := modifiedFileState.locationScope_of_current hcommentTop

            have hParentThreadRegisteredBase :
                ∀ parentId (h : parentId ∈ modifiedFileState.baseThreads.serverCommentIds),
                  comment₂.parent = some parentId →
                    modifiedFileState.baseThreads.serverCommentIds.get parentId h ∈
                      modifiedFileState.baseThreads.commentTreeNodes :=
              fun parentId h _ => modifiedFileState.baseThreads.hParentThreadRegistered_mem parentId h

            have hParentThreadRegisteredCurrent :
                ∀ parentId (h : parentId ∈ modifiedFileState.currentThreads.serverCommentIds),
                  comment₂.parent = some parentId →
                    modifiedFileState.currentThreads.serverCommentIds.get parentId h ∈
                      modifiedFileState.currentThreads.commentTreeNodes :=
              fun parentId h _ => modifiedFileState.currentThreads.hParentThreadRegistered_mem parentId h

            match hver : loc.version with
            | .base =>
              have hparentBase : ∀ parentId, comment₂.parent = some parentId →
                  parentId ∈ modifiedFileState.baseThreads.serverCommentIds := by
                rw [hver] at hparentFile; exact hparentFile

              let newBaseThreads := addCommentToThread modifiedFileState.baseThreads comment₂
                hHasBackendId hparentBase hParentThreadRegisteredBase hRefFreshBase hLocationScopeBase

              have hBaseThreadsFileScoped₁ : ∀ loc', loc' ∈ newBaseThreads.locationRoots.keys → loc'.isTopLevel = false :=
                addCommentToThread_locationRoots_isTopLevel modifiedFileState.baseThreads comment₂
                  hHasBackendId hparentBase hParentThreadRegisteredBase hRefFreshBase hLocationScopeBase false
                  modifiedFileState.hBaseThreadsFileScoped hcommentTop

              let newFileState : ModifiedFileState :=
                { modifiedFileState with
                  baseThreads := newBaseThreads,
                  selectedComment := none,
                  hSelectedCommentWellFormed := by simp,
                  hBaseThreadsFileScoped := hBaseThreadsFileScoped₁ }

              let commentManager₁ : CommentManager :=
                { s₀.commentManager with
                  comments := comments₁,
                  hCommentsKeyedByRef := hCommentsKeyedByRef₁,
                  hTopLevelThreadsPublished := hTopLevelThreadsPublished₁ }

              have hNewBaseThreadsContains : ∀ ref, newBaseThreads.commentTreeNodes.contains ref ↔
                  modifiedFileState.baseThreads.commentTreeNodes.contains ref ∨ ref = comment₂.ref :=
                addCommentToThread_commentTreeNodes_contains_iff modifiedFileState.baseThreads comment₂
                  hHasBackendId hparentBase hParentThreadRegisteredBase hRefFreshBase hLocationScopeBase

              let newState := s₀.fileManager.state.insert fileRef newFileState
              have hFileThreadsPublished₂ := s₀.hFileThreadsPublished_insert_base (newFileState := newFileState)
                (newState := newState) (newComments := comments₁) hOldContainsFileRef hgetval hbid0
                href2 hbackendId2 hNewBaseThreadsContains rfl rfl rfl rfl

              have hConsistentState₁ := s₀.fileManager.hConsistentState_insert hOldContainsFileRef newFileState

              let fileManager₁ : ModifiedFileManager :=
                { s₀.fileManager with
                  state := newState,
                  hConsistentState := hConsistentState₁ }
              let s₁ := { s₀ with
                          commentBeingEdited := none,
                          commentManager := commentManager₁,
                          fileManager := fileManager₁,
                          hCommentBeingEditedWellFormed := by simp,
                          hFileThreadsPublished := hFileThreadsPublished₂ }
              Result.mk (Except.ok comment₂) s₁
            | .current =>
              have hparentCurrent : ∀ parentId, comment₂.parent = some parentId →
                  parentId ∈ modifiedFileState.currentThreads.serverCommentIds := by
                rw [hver] at hparentFile; exact hparentFile

              let newCurrentThreads := addCommentToThread modifiedFileState.currentThreads comment₂
                hHasBackendId hparentCurrent hParentThreadRegisteredCurrent hRefFreshCurrent hLocationScopeCurrent

              have hCurrentThreadsFileScoped₁ : ∀ loc', loc' ∈ newCurrentThreads.locationRoots.keys →
                  loc'.isTopLevel = false :=
                addCommentToThread_locationRoots_isTopLevel modifiedFileState.currentThreads comment₂
                  hHasBackendId hparentCurrent hParentThreadRegisteredCurrent hRefFreshCurrent hLocationScopeCurrent false
                  modifiedFileState.hCurrentThreadsFileScoped hcommentTop

              let newFileState : ModifiedFileState :=
                { modifiedFileState with
                  currentThreads := newCurrentThreads,
                  selectedComment := none,
                  hSelectedCommentWellFormed := by simp,
                  hCurrentThreadsFileScoped := hCurrentThreadsFileScoped₁ }

              let commentManager₁ : CommentManager :=
                { s₀.commentManager with
                  comments := comments₁,
                  hCommentsKeyedByRef := hCommentsKeyedByRef₁,
                  hTopLevelThreadsPublished := hTopLevelThreadsPublished₁ }

              have hNewCurrentThreadsContains : ∀ ref, newCurrentThreads.commentTreeNodes.contains ref ↔
                  modifiedFileState.currentThreads.commentTreeNodes.contains ref ∨ ref = comment₂.ref :=
                addCommentToThread_commentTreeNodes_contains_iff modifiedFileState.currentThreads comment₂
                  hHasBackendId hparentCurrent hParentThreadRegisteredCurrent hRefFreshCurrent hLocationScopeCurrent

              let newState := s₀.fileManager.state.insert fileRef newFileState
              have hFileThreadsPublished₂ := s₀.hFileThreadsPublished_insert_current (newFileState := newFileState)
                (newState := newState) (newComments := comments₁) hOldContainsFileRef hgetval hbid0
                href2 hbackendId2 hNewCurrentThreadsContains rfl rfl rfl rfl

              have hConsistentState₁ := s₀.fileManager.hConsistentState_insert hOldContainsFileRef newFileState

              let fileManager₁ : ModifiedFileManager :=
                { s₀.fileManager with
                  state := newState,
                  hConsistentState := hConsistentState₁ }
              let s₁ := { s₀ with
                          commentBeingEdited := none,
                          commentManager := commentManager₁,
                          fileManager := fileManager₁,
                          hCommentBeingEditedWellFormed := by simp,
                          hFileThreadsPublished := hFileThreadsPublished₂ }
              Result.mk (Except.ok comment₂) s₁

private theorem completeCommentWithContent.rejectsEmptyContent (s₀ : State)
  (result : Result (Except String Comment))
  (hResultOfOp : completeCommentWithContent s₀ "" = result):
  ∃ msg, result.value = Except.error msg := by
  subst hResultOfOp
  simp [completeCommentWithContent]

private theorem completeCommentWithContent.preservesStateOnError (s₀ : State) (input : String):
  ∃ result, completeCommentWithContent s₀ input = result ∧ (¬ result.value.isOk → result.updatedState = s₀) := by
  obtain ⟨config, activeFile, cbe, cm, fm, hCBWF, hFTP⟩ := s₀
  refine ⟨_, rfl, ?_⟩
  refine Or.resolve_left ?_
  by_cases hEmpty : input.isEmpty
  · right; simp [completeCommentWithContent, hEmpty]
  · cases cbe with
    | none => right; simp [completeCommentWithContent, hEmpty]
    | some editedCommentRef =>
      match hCC : config.createComment
          { cm.get editedCommentRef with content := input } with
      | none => right; simp [completeCommentWithContent, hEmpty, hCC]
      | some serverId =>
        simp only [completeCommentWithContent, hEmpty, hCC]
        split
        · left; simp_all
        · split
          · left; rfl
          · split
            · right; rfl
            · split
              · left; rfl
              · left; rfl

private theorem completeCommentWithContent.failsWithNoCurrentEditedComment (s₀ : State)
  (input : String)
  (result : Result (Except String Comment))
  (hNotEmptyInput : input != "")
  (hResultOfOp : completeCommentWithContent s₀ input = result)
  (hNoActiveCommentBeingEdited : s₀.commentBeingEdited = none) :
  ∃ msg, result.value = Except.error msg := by
  subst hResultOfOp
  obtain ⟨config, activeFile, cbe, cm, fm, hCBWF, hFTP⟩ := s₀
  subst hNoActiveCommentBeingEdited
  have hEmpty : input.isEmpty = false := by
    rw [bne_iff_ne] at hNotEmptyInput
    simp [hNotEmptyInput]
  simp [completeCommentWithContent, hEmpty]

private theorem completeCommentWithContent.failsIfSavingCommentToServerFails (s₀ : State)
  (input : String)
  (result : Result (Except String Comment))
  (hNotEmptyInput : input != "")
  (comment₀ : Comment)
  (editedCommentRef : CommentRef)
  (hCommentBeingEdited : s₀.commentBeingEdited = some editedCommentRef)
  (hThisCommentIsBeingEdited : s₀.commentManager.get editedCommentRef = comment₀)
  (hResultOfOp : completeCommentWithContent s₀ input = result) :
  s₀.configuration.createComment { comment₀ with content := input } = none → ¬ result.value.isOk := by
  intro hCreateFails
  subst hResultOfOp
  obtain ⟨config, activeFile, cbe, cm, fm, hCBWF, hFTP⟩ := s₀
  dsimp only at hThisCommentIsBeingEdited hCreateFails
  subst hCommentBeingEdited
  subst hThisCommentIsBeingEdited
  have hEmpty : input.isEmpty = false := by
    rw [bne_iff_ne] at hNotEmptyInput
    simp [hNotEmptyInput]
  simp [completeCommentWithContent, hEmpty, hCreateFails, Except.isOk, Except.toBool]

public def cancelCommentCreation (s₀ : State) : Result Unit :=
  let s₁ := { s₀ with commentBeingEdited := none
                      hCommentBeingEditedWellFormed := by simp }
  Result.mk () s₁
