module

import Std

public import LgtmLean.Basic
public import LgtmLean.CreateThreads
import all LgtmLean.CreateThreads

public structure Result α where
  value : α
  updatedState : State

/-- Delete all of the comments in the current review state.

This is used to prepare to fetch an updated state from the server. -/
def resetCommentState (s₀ : State) : Result Unit :=
  let manager₁ := s₀.fileManager.resetCommentState
  let s₁ := { s₀ with
              commentBeingEdited := none,
              commentManager := CommentManager.empty,
              fileManager := manager₁,
              hCommentBeingEditedWellFormed := by simp,
              hFileThreadsPublished := s₀.fileManager.hFileThreadsPublished_resetCommentState CommentManager.empty.comments }
  Result.mk () s₁

private structure CommentBootstrapState where
  topLevelComments : List Comment
  hTopLevelCommentsAreTopLevel : ∀ c, c ∈ topLevelComments → c.location.isTopLevel
  baseComments : Std.HashMap ModifiedFileRef (List Comment)
  hBaseCommentsHaveBaseVersion : ∀ entry, entry ∈ baseComments.toList → (∀ c, c ∈ Prod.snd entry → ∃ loc, c.location = .fileLocation loc ∧ loc.version = .base)
  currentComments : Std.HashMap ModifiedFileRef (List Comment)
  hCurrentCommentsHaveCurrentVersion : ∀ entry, entry ∈ currentComments.toList → (∀ c, c ∈ Prod.snd entry → ∃ loc, c.location = .fileLocation loc ∧ loc.version = .current)

private def insertSingletonOrAppend (value : α) (current : Option (List α)) : Option (List α) :=
  match current with
  | none => some [value]
  | some values => some (value :: values)

/-- Inserting a comment located at `loc` (of version `version`) into the bucket keyed by
`loc.fileRef` preserves the invariant that every comment in the bucket has version `version`,
given that it held before the insertion. Shared by the `.base` and `.current` cases of
`groupComments.go`, which differ only in which field of `CommentBootstrapState` and which
`FileVersion` they instantiate this with. -/
private theorem alter_preserves_versionInvariant
    {version : FileVersion} {m : Std.HashMap ModifiedFileRef (List Comment)}
    (hInv : ∀ entry, entry ∈ m.toList →
      ∀ c, c ∈ Prod.snd entry → ∃ loc, c.location = .fileLocation loc ∧ loc.version = version)
    {c : Comment} {loc : CommentFileLocation}
    (hloc : c.location = .fileLocation loc) (hver : loc.version = version) :
    ∀ entry, entry ∈ (m.alter loc.fileRef (insertSingletonOrAppend c)).toList →
      ∀ c', c' ∈ Prod.snd entry → ∃ loc', c'.location = .fileLocation loc' ∧ loc'.version = version := by
  rintro ⟨k, v⟩ hentry c' hc'
  rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, Std.HashMap.getElem?_alter] at hentry
  split at hentry
  · unfold insertSingletonOrAppend at hentry
    split at hentry <;> cases hentry <;> rw [List.mem_cons] at hc' <;> rcases hc' with rfl | hc'
    · exact ⟨loc, hloc, hver⟩
    · nomatch hc'
    · exact ⟨loc, hloc, hver⟩
    · exact hInv (loc.fileRef, _) (by rw [Std.HashMap.mem_toList_iff_getElem?_eq_some]; assumption) c' hc'
  · exact hInv (k, v) (by rw [Std.HashMap.mem_toList_iff_getElem?_eq_some]; exact hentry) c' hc'

private def groupComments.go : List Comment → CommentBootstrapState → CommentBootstrapState
| [], bootstrapState => bootstrapState
| c :: cs, bootstrapState =>
  match hloc : c.location with
  | .topLevel =>
    groupComments.go cs { bootstrapState with
      topLevelComments := c :: bootstrapState.topLevelComments
      hTopLevelCommentsAreTopLevel := by
        intro c' hc'
        rw [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · simp [hloc]
        · exact bootstrapState.hTopLevelCommentsAreTopLevel c' hc' }
  | .fileLocation loc =>
    match hver : loc.version with
    | .base =>
      groupComments.go cs { bootstrapState with
        baseComments := bootstrapState.baseComments.alter loc.fileRef (insertSingletonOrAppend c)
        hBaseCommentsHaveBaseVersion :=
          alter_preserves_versionInvariant bootstrapState.hBaseCommentsHaveBaseVersion hloc hver }
    | .current =>
      groupComments.go cs { bootstrapState with
        currentComments := bootstrapState.currentComments.alter loc.fileRef (insertSingletonOrAppend c)
        hCurrentCommentsHaveCurrentVersion :=
          alter_preserves_versionInvariant bootstrapState.hCurrentCommentsHaveCurrentVersion hloc hver }

private def groupComments (comments : List Comment) : CommentBootstrapState :=
  groupComments.go comments (CommentBootstrapState.mk [] (by simp) Std.HashMap.emptyWithCapacity (by simp)
    Std.HashMap.emptyWithCapacity (by simp))

private def commentsByRef.go : List Comment → Std.HashMap CommentRef Comment → Std.HashMap CommentRef Comment
| [], m => m
| c :: cs, m => commentsByRef.go cs (m.insert c.ref c)

private theorem commentsByRef.go_hCommentsKeyedByRef (comments : List Comment) (m : Std.HashMap CommentRef Comment)
    (hInv : ∀ ref (h : m.contains ref), (m.get ref h).ref = ref) :
    ∀ ref (h : (commentsByRef.go comments m).contains ref), ((commentsByRef.go comments m).get ref h).ref = ref := by
  induction comments generalizing m with
  | nil => exact hInv
  | cons c cs ih =>
    apply ih
    intro ref h
    by_cases heq : c.ref = ref
    · subst heq; rw [Std.HashMap.get_insert_self]
    · have hne : ¬ (c.ref == ref) := by simpa [beq_iff_eq] using heq
      have hc : m.contains ref := by
        have h' := h
        rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at h'
        rcases h' with h1 | h1
        · exact absurd h1 heq
        · exact h1
      rw [Std.HashMap.get_insert_of_ne hne h hc]
      exact hInv ref hc

private theorem commentsByRef.go_hPublished (comments : List Comment) (m : Std.HashMap CommentRef Comment)
    (hAll : ∀ c, c ∈ comments → c.backendId.isSome)
    (hInv : ∀ ref (h : m.contains ref), (m.get ref h).backendId.isSome) :
    ∀ ref (h : (commentsByRef.go comments m).contains ref),
      ((commentsByRef.go comments m).get ref h).backendId.isSome := by
  induction comments generalizing m with
  | nil => exact hInv
  | cons c cs ih =>
    apply ih
    · intro c' hc'; exact hAll c' (List.mem_cons_of_mem _ hc')
    · intro ref h
      by_cases heq : c.ref = ref
      · subst heq; rw [Std.HashMap.get_insert_self]; exact hAll c List.mem_cons_self
      · have hne : ¬ (c.ref == ref) := by simpa [beq_iff_eq] using heq
        have hc : m.contains ref := by
          have h' := h
          rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at h'
          rcases h' with h1 | h1
          · exact absurd h1 heq
          · exact h1
        rw [Std.HashMap.get_insert_of_ne hne h hc]
        exact hInv ref hc

private theorem commentsByRef.go_contains_mono (comments : List Comment) (m : Std.HashMap CommentRef Comment)
    (ref : CommentRef) (h : m.contains ref) : (commentsByRef.go comments m).contains ref := by
  induction comments generalizing m with
  | nil => exact h
  | cons c cs ih =>
    apply ih
    rw [Std.HashMap.contains_insert, Bool.or_eq_true]
    exact Or.inr h

private theorem commentsByRef.go_contains_of_mem (comments : List Comment) (m : Std.HashMap CommentRef Comment)
    (c : Comment) (hc : c ∈ comments) : (commentsByRef.go comments m).contains c.ref := by
  induction comments generalizing m with
  | nil => cases hc
  | cons c' cs ih =>
    rw [List.mem_cons] at hc
    rcases hc with rfl | hc
    · apply commentsByRef.go_contains_mono cs (m.insert c.ref c) c.ref
      rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq]
      exact Or.inl rfl
    · exact ih (m.insert c'.ref c') hc

/-- Builds the `CommentManager.comments` map for a batch of comments received from the server,
keyed by `.ref`. -/
private def commentsByRef (comments : List Comment) : Std.HashMap CommentRef Comment :=
  commentsByRef.go comments Std.HashMap.emptyWithCapacity

private theorem commentsByRef_hCommentsKeyedByRef (comments : List Comment) :
    ∀ ref (h : (commentsByRef comments).contains ref), ((commentsByRef comments).get ref h).ref = ref :=
  commentsByRef.go_hCommentsKeyedByRef comments Std.HashMap.emptyWithCapacity (by simp)

private theorem commentsByRef_hPublished (comments : List Comment)
    (hAll : ∀ c, c ∈ comments → c.backendId.isSome) :
    ∀ ref (h : (commentsByRef comments).contains ref), ((commentsByRef comments).get ref h).backendId.isSome :=
  commentsByRef.go_hPublished comments Std.HashMap.emptyWithCapacity hAll (by simp)

private theorem commentsByRef_contains_of_mem (comments : List Comment) (c : Comment) (hc : c ∈ comments) :
    (commentsByRef comments).contains c.ref :=
  commentsByRef.go_contains_of_mem comments Std.HashMap.emptyWithCapacity c hc

/-- `addRemoteComments` validates a server-provided comment batch against these predicates before
assembling threads from it, via `if h : ... then ... else ...`. Instance search won't unfold a
plain `def` on its own (and these `def`s can't be marked `@[expose]`/unfolded from a `public`
declaration without extra bridge lemmas), so each predicate needs its own `Decidable` instance
spelled out here; keeping them `private` (rather than adding them to `CreateThreads.lean`) sidesteps
that entirely, since a private declaration gets full local transparency. -/
private instance allCommentsHaveBackendId.decidable (comments : List Comment) :
    Decidable (allCommentsHaveBackendId comments) := by
  unfold allCommentsHaveBackendId; infer_instance

private instance allParentsInComments.decidable (comments : List Comment) :
    Decidable (allParentsInComments comments) := by
  unfold allParentsInComments; infer_instance

private instance commentRefsNodup.decidable (comments : List Comment) :
    Decidable (commentRefsNodup comments) := by
  unfold commentRefsNodup; infer_instance

private instance parentsCreatedBefore.decidable (comments : List Comment) :
    Decidable (parentsCreatedBefore comments) := by
  unfold parentsCreatedBefore; infer_instance

/-- Bulk-loads a fresh batch of comments from the server, replacing whatever comment state was
there before.

This only threads the batch's top-level (unattached) comments into `commentManager.topLevelThreads`
so far; per-file (`.base` / `.current`) comments are grouped by `groupComments` but not yet threaded
into `fileManager`'s per-file `baseThreads` / `currentThreads` -- that's tracked as follow-up work.

Fails (leaving the state unchanged) if the server's batch doesn't satisfy the structural invariants
`assembleCommentTrees` needs (every comment has a backend id, every referenced parent is in the
batch, refs are unique, and parents predate their replies) -- these can't be guaranteed by
`getRemoteConversations`'s type, since the batch comes from outside the Lean model. -/
public def addRemoteComments (s₀ : State) : Result (Except String Unit) :=
  match s₀.configuration.getRemoteConversations s₀.fileManager with
  | none => Result.mk (Except.ok ()) s₀
  | some comments =>
    let bootstrapState := groupComments comments
    if h : allCommentsHaveBackendId bootstrapState.topLevelComments ∧
        allParentsInComments bootstrapState.topLevelComments ∧
        commentRefsNodup bootstrapState.topLevelComments ∧
        parentsCreatedBefore bootstrapState.topLevelComments then
      let ⟨hBackend, hParents, hNodup, hBefore⟩ := h
      let hSameLocation : commentsAllInSameFileOrAllTopLevel bootstrapState.topLevelComments :=
        Or.inl bootstrapState.hTopLevelCommentsAreTopLevel
      let topLevelThreads := assembleCommentTrees bootstrapState.topLevelComments hSameLocation hBackend hParents
        hNodup hBefore
      let commentManager₁ : CommentManager :=
        { comments := commentsByRef bootstrapState.topLevelComments,
          topLevelThreads := topLevelThreads,
          selectedComment := none,
          hSelectedCommentWellFormed := by simp,
          hCommentsKeyedByRef := commentsByRef_hCommentsKeyedByRef bootstrapState.topLevelComments,
          hTopLevelThreadsAllTopLevel := assembleCommentTrees_locationRoots_isTopLevel
            bootstrapState.topLevelComments hSameLocation bootstrapState.hTopLevelCommentsAreTopLevel hBackend
            hParents hNodup hBefore,
          hTopLevelThreadsPublished := fun ref h' => by
            obtain ⟨c, hc, hcref⟩ := (assembleCommentTrees_commentTreeNodes_contains_iff
              bootstrapState.topLevelComments hSameLocation hBackend hParents hNodup hBefore ref).mp h'
            exact ⟨hcref ▸ commentsByRef_contains_of_mem bootstrapState.topLevelComments c hc,
              commentsByRef_hPublished bootstrapState.topLevelComments hBackend ref _⟩ }
      let s₁ : State :=
        { s₀ with
          commentBeingEdited := none,
          commentManager := commentManager₁,
          fileManager := s₀.fileManager.resetCommentState,
          hCommentBeingEditedWellFormed := by simp,
          hFileThreadsPublished :=
            s₀.fileManager.hFileThreadsPublished_resetCommentState commentManager₁.comments }
      Result.mk (Except.ok ()) s₁
    else
      Result.mk (Except.error "Received malformed comment data from the server") s₀

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
    | some comment₀ =>
      let comment₁ := { comment₀ with content := newContent }
      match s₀.configuration.createComment comment₁ with
      | none => Result.mk (Except.error "Failed to create the comment on the server") s₀
      | some serverId =>
        let comment₂ : Comment := { comment₁ with backendId := serverId }
        have hbackendId2 : comment₂.backendId = some serverId := rfl
        have hHasBackendId : comment₂.backendId.isSome := by rw [hbackendId2]; rfl

        have hDerived := s₀.commentManager.get_of_commentBeingEditedWellFormed s₀.fileManager comment₀
          (s₀.hCommentBeingEditedWellFormed comment₀ hBeingEdited)
        have hFresh0 : ¬ s₀.commentManager.comments.contains comment₀.ref := hDerived.1
        have hparent0 := hDerived.2.2

        have href2 : comment₂.ref = comment₀.ref := rfl

        let comments₁ := s₀.commentManager.comments.insert comment₀.ref comment₂

        have hCommentsKeyedByRef₁ : ∀ ref (h : comments₁.contains ref), (comments₁.get ref h).ref = ref :=
          s₀.commentManager.hCommentsKeyedByRef_insert comment₀.ref comment₂ href2

        -- Inserting the (freshly-published) being-edited comment into `comments` can't disturb any
        -- other ref's published status: it either was already there and is untouched, or it *is*
        -- `comment₀.ref`, which was fresh (unregistered) and so can't have been the ref some other
        -- invariant already certified as published.
        have hPreservePublished := s₀.commentManager.preservePublished_insert hFresh0 comment₂

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
            exact s₀.commentManager.notMem_topLevelThreads_of_unpublished comment₀.ref hFresh0

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
            s₀.commentManager.hTopLevelThreadsPublished_insert comment₀.ref comment₂ href2
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
          -- FIXME: Change this from a find to a lookup of the modifiedFileState.ref instead
          match hfound : s₀.fileManager.state.toList.find? (λ (_, modifiedFileState) => modifiedFileState.ref == loc.fileRef) with
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
              exact s₀.notMem_baseThreads_of_unpublished hFresh0 hOldContainsFileRef

            have hRefFreshCurrent : comment₂.ref ∉ modifiedFileState.currentThreads.commentTreeNodes := by
              rw [href2, ← hgetval]
              exact s₀.notMem_currentThreads_of_unpublished hFresh0 hOldContainsFileRef

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
                (newState := newState) (newComments := comments₁) hOldContainsFileRef hgetval hFresh0
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
                (newState := newState) (newComments := comments₁) hOldContainsFileRef hgetval hFresh0
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
    | some comment₀ =>
      match hCC : config.createComment
          { comment₀ with content := input } with
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
  (hCommentBeingEdited : s₀.commentBeingEdited = some comment₀)
  (hResultOfOp : completeCommentWithContent s₀ input = result) :
  s₀.configuration.createComment { comment₀ with content := input } = none → ¬ result.value.isOk := by
  intro hCreateFails
  subst hResultOfOp
  obtain ⟨config, activeFile, cbe, cm, fm, hCBWF, hFTP⟩ := s₀
  dsimp only at hCreateFails
  subst hCommentBeingEdited
  have hEmpty : input.isEmpty = false := by
    rw [bne_iff_ne] at hNotEmptyInput
    simp [hNotEmptyInput]
  simp [completeCommentWithContent, hEmpty, hCreateFails, Except.isOk, Except.toBool]

public def cancelCommentCreation (s₀ : State) : Result Unit :=
  let s₁ := { s₀ with commentBeingEdited := none
                      hCommentBeingEditedWellFormed := by simp }
  Result.mk () s₁

private theorem cancelCommentCreation.ensuresNoCommentBeingEdited (s₀ : State)
  (result : Result Unit)
  (hResultOfOp : cancelCommentCreation s₀ = result) :
  result.updatedState.commentBeingEdited = none := by
  subst hResultOfOp
  simp [cancelCommentCreation]
