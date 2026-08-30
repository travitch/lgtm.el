module

import Std

public import LgtmLean.Basic
public import LgtmLean.CreateThreads


/-- Delete all of the comments in the current review state.

This is used to prepare to fetch an updated state from the server. -/
public def resetCommentState : LgtmM Unit := do
  let s₀ ← get
  let manager₁ := s₀.fileManager.resetCommentState
  set { s₀ with
    commentBeingEdited := none,
    commentManager := CommentManager.empty,
    fileManager := manager₁,
    hCommentBeingEditedWellFormed := by simp,
    hFileThreadsPublished := s₀.fileManager.hFileThreadsPublished_resetCommentState CommentManager.empty.comments }


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
      have hPreservePublished : ∀ ref (h : s₀.commentManager.comments.contains ref),
          (s₀.commentManager.comments.get ref h).backendId.isSome →
          ∃ h' : comments₁.contains ref, (comments₁.get ref h').backendId.isSome := by
        intro ref h hpub
        have hne : ref ≠ editedCommentRef := by
          intro heq
          subst heq
          have hgetEq : s₀.commentManager.comments.get ref h = comment₀ :=
            (s₀.commentManager.get_eq_getComments h).symm
          rw [hgetEq, hbid0] at hpub
          simp at hpub
        have hc : comments₁.contains ref := by
          rw [Std.HashMap.contains_insert, Bool.or_eq_true]
          exact Or.inr h
        refine ⟨hc, ?_⟩
        have hne' : ¬ (editedCommentRef == ref) := by simpa [beq_iff_eq] using (Ne.symm hne)
        rw [Std.HashMap.get_insert_of_ne hne' hc h]
        exact hpub

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
        StateT.set { s₀ with
          commentBeingEdited := none,
          commentManager := commentManager₁,
          hCommentBeingEditedWellFormed := by simp,
          hFileThreadsPublished := hFileThreadsPublished₁ }
      | .fileLocation loc =>
        match hfound : s₀.fileManager.state.toList.find? (λ (_, modifiedFileState) => modifiedFileState.fileRef == loc.fileRef) with
        | none => throw "Unexpected file"
        | some (fileRef, modifiedFileState) =>
          have hmem : (fileRef, modifiedFileState) ∈ s₀.fileManager.state.toList := List.mem_of_find?_eq_some hfound
          have hpred := List.find?_some hfound

          have hgetElem? : s₀.fileManager.state[fileRef]? = some modifiedFileState :=
            (Std.HashMap.mem_toList_iff_getElem?_eq_some).mp hmem
          have hOldContainsFileRef : s₀.fileManager.state.contains fileRef := by
            rw [Std.HashMap.contains_eq_isSome_getElem?, hgetElem?]; rfl
          have hgetval : s₀.fileManager.state.get fileRef hOldContainsFileRef = modifiedFileState := by
            obtain ⟨_, hval⟩ := Std.HashMap.getElem?_eq_some_iff.mp hgetElem?
            exact hval

          have hOldPublishedFile := hgetval ▸ s₀.hFileThreadsPublished fileRef hOldContainsFileRef

          -- `topLevelThreads` is untouched by a file-scoped comment; only `comments` grows.
          have hTopLevelThreadsPublished₁ : ∀ ref' (h : s₀.commentManager.topLevelThreads.commentTreeNodes.contains ref'),
              ∃ h' : comments₁.contains ref', (comments₁.get ref' h').backendId.isSome := by
            intro ref' h
            obtain ⟨hcOld, hpubOld⟩ := s₀.commentManager.hTopLevelThreadsPublished ref' h
            exact hPreservePublished ref' hcOld hpubOld

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
            rw [href2]
            intro hmemPool
            obtain ⟨hExists', hSome⟩ := hOldPublishedFile.1 editedCommentRef (Std.HashMap.mem_iff_contains.mp hmemPool)
            have hEqGet : s₀.commentManager.comments.get editedCommentRef hExists' = comment₀ :=
              (s₀.commentManager.get_eq_getComments hExists').symm
            rw [hEqGet, hbid0] at hSome
            simp at hSome

          have hRefFreshCurrent : comment₂.ref ∉ modifiedFileState.currentThreads.commentTreeNodes := by
            rw [href2]
            intro hmemPool
            obtain ⟨hExists', hSome⟩ := hOldPublishedFile.2 editedCommentRef (Std.HashMap.mem_iff_contains.mp hmemPool)
            have hEqGet : s₀.commentManager.comments.get editedCommentRef hExists' = comment₀ :=
              (s₀.commentManager.get_eq_getComments hExists').symm
            rw [hEqGet, hbid0] at hSome
            simp at hSome

          have hLocationScopeBase : ∀ loc', loc' ∈ modifiedFileState.baseThreads.locationRoots.keys →
              loc'.isTopLevel = comment₂.location.asThreadLocation.isTopLevel := by
            rw [hcommentTop]
            exact modifiedFileState.hBaseThreadsFileScoped

          have hLocationScopeCurrent : ∀ loc', loc' ∈ modifiedFileState.currentThreads.locationRoots.keys →
              loc'.isTopLevel = comment₂.location.asThreadLocation.isTopLevel := by
            rw [hcommentTop]
            exact modifiedFileState.hCurrentThreadsFileScoped

          have hParentThreadRegisteredBase :
              ∀ parentId (h : parentId ∈ modifiedFileState.baseThreads.serverCommentIds),
                comment₂.parent = some parentId →
                  modifiedFileState.baseThreads.serverCommentIds.get parentId h ∈
                    modifiedFileState.baseThreads.commentTreeNodes :=
            fun parentId h _ => Std.HashMap.mem_iff_contains.mpr
              (modifiedFileState.baseThreads.hServerCommentIdsRegistered parentId (Std.HashMap.mem_iff_contains.mp h))

          have hParentThreadRegisteredCurrent :
              ∀ parentId (h : parentId ∈ modifiedFileState.currentThreads.serverCommentIds),
                comment₂.parent = some parentId →
                  modifiedFileState.currentThreads.serverCommentIds.get parentId h ∈
                    modifiedFileState.currentThreads.commentTreeNodes :=
            fun parentId h _ => Std.HashMap.mem_iff_contains.mpr
              (modifiedFileState.currentThreads.hServerCommentIdsRegistered parentId
                (Std.HashMap.mem_iff_contains.mp h))

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
            have hFileThreadsPublished₂ : ∀ modifiedFileRef' (h : newState.contains modifiedFileRef'),
                (∀ ref (hc : (newState.get modifiedFileRef' h).baseThreads.commentTreeNodes.contains ref),
                  ∃ h' : comments₁.contains ref, (comments₁.get ref h').backendId.isSome) ∧
                (∀ ref (hc : (newState.get modifiedFileRef' h).currentThreads.commentTreeNodes.contains ref),
                  ∃ h' : comments₁.contains ref, (comments₁.get ref h').backendId.isSome) := by
              intro modifiedFileRef' h
              by_cases heq : fileRef = modifiedFileRef'
              · subst heq
                rw [Std.HashMap.get_insert_self]
                refine ⟨fun ref hc => ?_, fun ref hc => ?_⟩
                · have hc' : newBaseThreads.commentTreeNodes.contains ref := hc
                  rcases (hNewBaseThreadsContains ref).mp hc' with hold | hnew
                  · obtain ⟨hcOld, hpubOld⟩ := hOldPublishedFile.1 ref hold
                    exact hPreservePublished ref hcOld hpubOld
                  · have hcNew : comments₁.contains editedCommentRef := Std.HashMap.contains_insert_self
                    rw [hnew, href2]
                    refine ⟨hcNew, ?_⟩
                    rw [Std.HashMap.get_insert_self, hbackendId2]
                    rfl
                · obtain ⟨hcOld, hpubOld⟩ := hOldPublishedFile.2 ref hc
                  exact hPreservePublished ref hcOld hpubOld
              · have hne'' : ¬ (fileRef == modifiedFileRef') := by simpa [beq_iff_eq] using heq
                have hcOld : s₀.fileManager.state.contains modifiedFileRef' := by
                  have h' := h
                  rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at h'
                  rcases h' with h1 | h1
                  · exact absurd h1 heq
                  · exact h1
                rw [Std.HashMap.get_insert_of_ne hne'' h hcOld]
                obtain ⟨hBase, hCurrent⟩ := s₀.hFileThreadsPublished modifiedFileRef' hcOld
                refine ⟨fun ref hc => ?_, fun ref hc => ?_⟩
                · obtain ⟨hc', hpub'⟩ := hBase ref hc
                  exact hPreservePublished ref hc' hpub'
                · obtain ⟨hc', hpub'⟩ := hCurrent ref hc
                  exact hPreservePublished ref hc' hpub'

            have hConsistentState₁ : ∀ modifiedFile, modifiedFile ∈ s₀.fileManager.modifiedFiles ↔
                newState.contains modifiedFile := by
              intro modifiedFile
              rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq]
              constructor
              · intro hmf
                by_cases heq : fileRef = modifiedFile
                · exact Or.inl heq
                · exact Or.inr ((s₀.fileManager.hConsistentState modifiedFile).mp hmf)
              · rintro (heq | hc)
                · rw [← heq]; exact (s₀.fileManager.hConsistentState fileRef).mpr hOldContainsFileRef
                · exact (s₀.fileManager.hConsistentState modifiedFile).mpr hc

            let fileManager₁ : ModifiedFileManager :=
              { s₀.fileManager with
                state := newState,
                hConsistentState := hConsistentState₁ }
            StateT.set { s₀ with
              commentBeingEdited := none,
              commentManager := commentManager₁,
              fileManager := fileManager₁,
              hCommentBeingEditedWellFormed := by simp,
              hFileThreadsPublished := hFileThreadsPublished₂ }
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
            have hFileThreadsPublished₂ : ∀ modifiedFileRef' (h : newState.contains modifiedFileRef'),
                (∀ ref (hc : (newState.get modifiedFileRef' h).baseThreads.commentTreeNodes.contains ref),
                  ∃ h' : comments₁.contains ref, (comments₁.get ref h').backendId.isSome) ∧
                (∀ ref (hc : (newState.get modifiedFileRef' h).currentThreads.commentTreeNodes.contains ref),
                  ∃ h' : comments₁.contains ref, (comments₁.get ref h').backendId.isSome) := by
              intro modifiedFileRef' h
              by_cases heq : fileRef = modifiedFileRef'
              · subst heq
                rw [Std.HashMap.get_insert_self]
                refine ⟨fun ref hc => ?_, fun ref hc => ?_⟩
                · obtain ⟨hcOld, hpubOld⟩ := hOldPublishedFile.1 ref hc
                  exact hPreservePublished ref hcOld hpubOld
                · have hc' : newCurrentThreads.commentTreeNodes.contains ref := hc
                  rcases (hNewCurrentThreadsContains ref).mp hc' with hold | hnew
                  · obtain ⟨hcOld, hpubOld⟩ := hOldPublishedFile.2 ref hold
                    exact hPreservePublished ref hcOld hpubOld
                  · have hcNew : comments₁.contains editedCommentRef := Std.HashMap.contains_insert_self
                    rw [hnew, href2]
                    refine ⟨hcNew, ?_⟩
                    rw [Std.HashMap.get_insert_self, hbackendId2]
                    rfl
              · have hne'' : ¬ (fileRef == modifiedFileRef') := by simpa [beq_iff_eq] using heq
                have hcOld : s₀.fileManager.state.contains modifiedFileRef' := by
                  have h' := h
                  rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at h'
                  rcases h' with h1 | h1
                  · exact absurd h1 heq
                  · exact h1
                rw [Std.HashMap.get_insert_of_ne hne'' h hcOld]
                obtain ⟨hBase, hCurrent⟩ := s₀.hFileThreadsPublished modifiedFileRef' hcOld
                refine ⟨fun ref hc => ?_, fun ref hc => ?_⟩
                · obtain ⟨hc', hpub'⟩ := hBase ref hc
                  exact hPreservePublished ref hc' hpub'
                · obtain ⟨hc', hpub'⟩ := hCurrent ref hc
                  exact hPreservePublished ref hc' hpub'

            have hConsistentState₁ : ∀ modifiedFile, modifiedFile ∈ s₀.fileManager.modifiedFiles ↔
                newState.contains modifiedFile := by
              intro modifiedFile
              rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq]
              constructor
              · intro hmf
                by_cases heq : fileRef = modifiedFile
                · exact Or.inl heq
                · exact Or.inr ((s₀.fileManager.hConsistentState modifiedFile).mp hmf)
              · rintro (heq | hc)
                · rw [← heq]; exact (s₀.fileManager.hConsistentState fileRef).mpr hOldContainsFileRef
                · exact (s₀.fileManager.hConsistentState modifiedFile).mpr hc

            let fileManager₁ : ModifiedFileManager :=
              { s₀.fileManager with
                state := newState,
                hConsistentState := hConsistentState₁ }
            StateT.set { s₀ with
              commentBeingEdited := none,
              commentManager := commentManager₁,
              fileManager := fileManager₁,
              hCommentBeingEditedWellFormed := by simp,
              hFileThreadsPublished := hFileThreadsPublished₂ }

      pure comment₂
