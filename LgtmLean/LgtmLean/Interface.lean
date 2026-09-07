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
public def resetCommentState (s₀ : State) : Result Unit :=
  let manager₁ := s₀.fileManager.resetCommentState
  let s₁ := { s₀ with
              commentBeingEdited := none,
              commentManager := CommentManager.empty,
              fileManager := manager₁,
              hCommentBeingEditedWellFormed := by simp,
              hFileThreadsPublished := s₀.fileManager.hFileThreadsPublished_resetCommentState CommentManager.empty.comments }
  Result.mk () s₁

public structure CommentBootstrapState where
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

public def groupComments.go (comments : List Comment) (bootstrapState : CommentBootstrapState) : CommentBootstrapState :=
match comments with
| [] => bootstrapState
| c :: cs =>
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

public def groupComments (comments : List Comment) : CommentBootstrapState :=
  groupComments.go comments (CommentBootstrapState.mk [] (by simp) Std.HashMap.emptyWithCapacity (by simp)
    Std.HashMap.emptyWithCapacity (by simp))

public def commentsByRef.go (comments : List Comment) (m : Std.HashMap CommentRef Comment) : Std.HashMap CommentRef Comment :=
match comments with
| [] => m
| c :: cs => commentsByRef.go cs (m.insert c.ref c)

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
public def commentsByRef (comments : List Comment) : Std.HashMap CommentRef Comment :=
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

/-- `(m.insert k v).contains k'` doesn't depend on `v` when `k` was already present: inserting at an
already-tracked key can't add or remove any other key (or `k` itself). Used by
`FileThreadsBootstrapState.applyBase` / `.applyCurrent` to show each per-file update leaves
`ModifiedFileManager.state`'s key set (hence `hConsistentState`) untouched. -/
private theorem contains_insert_of_contains {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Std.HashMap α β} {k : α} (hk : m.contains k) (v : β) (k' : α) :
    (m.insert k v).contains k' = m.contains k' := by
  rw [Std.HashMap.contains_insert]
  by_cases heq : (k == k') = true
  · simp only [heq, Bool.true_or]
    exact ((Std.HashMap.contains_congr heq).symm.trans hk).symm
  · rw [Bool.not_eq_true] at heq
    rw [heq, Bool.false_or]

/-- Accumulates per-file `baseThreads` / `currentThreads` updates while bulk-loading comments from
the server: `state` starts as `fileManager.resetCommentState.state` (every file's threads empty)
and is updated one file at a time by `applyBase` / `.applyCurrent`. `hSameContains` says the update
never changes which files are tracked (only an already-tracked file's `ModifiedFileState` can be
replaced), which is what lets the final `ModifiedFileManager.hConsistentState` be recovered from the
original `fileManager.resetCommentState`'s. `hPublished` is the `State.hFileThreadsPublished`
invariant relative to the final, fixed `comments₁` map. -/
public structure FileThreadsBootstrapState (origState : Std.HashMap ModifiedFileRef ModifiedFileState)
    (comments₁ : Std.HashMap CommentRef Comment) where
  state : Std.HashMap ModifiedFileRef ModifiedFileState
  hSameContains : ∀ mf, state.contains mf = origState.contains mf
  hPublished : ∀ fileRef (h : state.contains fileRef),
    (∀ ref (_hc : (state.get fileRef h).baseThreads.commentTreeNodes.contains ref),
      ∃ h' : comments₁.contains ref, (comments₁.get ref h').backendId.isSome) ∧
    (∀ ref (_hc : (state.get fileRef h).currentThreads.commentTreeNodes.contains ref),
      ∃ h' : comments₁.contains ref, (comments₁.get ref h').backendId.isSome)

/-- Threads one file's batch of base-version comments into that file's `baseThreads`, leaving
`currentThreads` (and every other file) untouched. `hSubset` packages what the caller already knows
about how `cs` relates to the final `comments₁` map (via `commentsByRef`), decoupling this
per-file step from the global bookkeeping needed to establish it. -/
public def FileThreadsBootstrapState.applyBase
    {origState : Std.HashMap ModifiedFileRef ModifiedFileState} {comments₁ : Std.HashMap CommentRef Comment}
    (bs : FileThreadsBootstrapState origState comments₁)
    (fileRef : ModifiedFileRef) (cs : List Comment)
    (hFound : origState.contains fileRef)
    (hSameLoc : commentsAllInSameFileOrAllTopLevel cs)
    (hFileLocated : ∀ c, c ∈ cs → ∃ loc, c.location = CommentLocation.fileLocation loc)
    (hBackend : allCommentsHaveBackendId cs) (hParents : allParentsInComments cs)
    (hNodup : commentRefsNodup cs) (hBefore : parentsCreatedBefore cs)
    (hSubset : ∀ c, c ∈ cs → ∃ h' : comments₁.contains c.ref, (comments₁.get c.ref h').backendId.isSome) :
    FileThreadsBootstrapState origState comments₁ :=
  have hOldState : bs.state.contains fileRef := by rw [bs.hSameContains]; exact hFound
  let oldFileState := bs.state.get fileRef hOldState
  let newBaseThreads := assembleCommentTrees cs hSameLoc hBackend hParents hNodup hBefore
  let newFileState : ModifiedFileState :=
    { oldFileState with
      selectedComment := none,
      baseThreads := newBaseThreads,
      hSelectedCommentWellFormed := by simp,
      hBaseThreadsFileScoped := assembleCommentTrees_locationRoots_not_isTopLevel cs hSameLoc hFileLocated hBackend
        hParents hNodup hBefore }
  { state := bs.state.insert fileRef newFileState,
    hSameContains := fun mf => by
      rw [contains_insert_of_contains hOldState, bs.hSameContains],
    hPublished := fun fileRef' h => by
      by_cases heq : fileRef = fileRef'
      · subst heq
        rw [Std.HashMap.get_insert_self]
        refine ⟨fun ref hc => ?_, fun ref hc => ?_⟩
        · obtain ⟨c, hcmem, hcref⟩ := (assembleCommentTrees_commentTreeNodes_contains_iff cs hSameLoc hBackend
            hParents hNodup hBefore ref).mp hc
          exact hcref ▸ hSubset c hcmem
        · exact (bs.hPublished fileRef hOldState).2 ref hc
      · have hne : ¬ (fileRef == fileRef') := fun h => heq (beq_iff_eq.mp h)
        have hc' : bs.state.contains fileRef' := by
          have h2 := h
          rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at h2
          rcases h2 with h1 | h1
          · exact absurd h1 heq
          · exact h1
        rw [Std.HashMap.get_insert_of_ne hne h hc']
        exact bs.hPublished fileRef' hc' }

/-- The `.current`-version counterpart of `FileThreadsBootstrapState.applyBase`. -/
public def FileThreadsBootstrapState.applyCurrent
    {origState : Std.HashMap ModifiedFileRef ModifiedFileState} {comments₁ : Std.HashMap CommentRef Comment}
    (bs : FileThreadsBootstrapState origState comments₁)
    (fileRef : ModifiedFileRef) (cs : List Comment)
    (hFound : origState.contains fileRef)
    (hSameLoc : commentsAllInSameFileOrAllTopLevel cs)
    (hFileLocated : ∀ c, c ∈ cs → ∃ loc, c.location = CommentLocation.fileLocation loc)
    (hBackend : allCommentsHaveBackendId cs) (hParents : allParentsInComments cs)
    (hNodup : commentRefsNodup cs) (hBefore : parentsCreatedBefore cs)
    (hSubset : ∀ c, c ∈ cs → ∃ h' : comments₁.contains c.ref, (comments₁.get c.ref h').backendId.isSome) :
    FileThreadsBootstrapState origState comments₁ :=
  have hOldState : bs.state.contains fileRef := by rw [bs.hSameContains]; exact hFound
  let oldFileState := bs.state.get fileRef hOldState
  let newCurrentThreads := assembleCommentTrees cs hSameLoc hBackend hParents hNodup hBefore
  let newFileState : ModifiedFileState :=
    { oldFileState with
      selectedComment := none,
      currentThreads := newCurrentThreads,
      hSelectedCommentWellFormed := by simp,
      hCurrentThreadsFileScoped := assembleCommentTrees_locationRoots_not_isTopLevel cs hSameLoc hFileLocated hBackend
        hParents hNodup hBefore }
  { state := bs.state.insert fileRef newFileState,
    hSameContains := fun mf => by
      rw [contains_insert_of_contains hOldState, bs.hSameContains],
    hPublished := fun fileRef' h => by
      by_cases heq : fileRef = fileRef'
      · subst heq
        rw [Std.HashMap.get_insert_self]
        refine ⟨fun ref hc => ?_, fun ref hc => ?_⟩
        · exact (bs.hPublished fileRef hOldState).1 ref hc
        · obtain ⟨c, hcmem, hcref⟩ := (assembleCommentTrees_commentTreeNodes_contains_iff cs hSameLoc hBackend
            hParents hNodup hBefore ref).mp hc
          exact hcref ▸ hSubset c hcmem
      · have hne : ¬ (fileRef == fileRef') := fun h => heq (beq_iff_eq.mp h)
        have hc' : bs.state.contains fileRef' := by
          have h2 := h
          rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at h2
          rcases h2 with h1 | h1
          · exact absurd h1 heq
          · exact h1
        rw [Std.HashMap.get_insert_of_ne hne h hc']
        exact bs.hPublished fileRef' hc' }

/-- Folds `FileThreadsBootstrapState.applyBase` over every `(fileRef, comments)` entry of a file
bucket (e.g. `bootstrapState.baseComments.toList`), threading the per-entry validity facts through
via `List.mem_cons_of_mem`/`List.mem_cons_self` at each step (mirroring `commentsByRef.go`'s
threading style). -/
public def applyBaseThreads.go (comments₁ : Std.HashMap CommentRef Comment)
    (origState : Std.HashMap ModifiedFileRef ModifiedFileState)
    (l : List (ModifiedFileRef × List Comment))
    (hAll : ∀ entry, entry ∈ l →
      origState.contains entry.1 ∧ commentsAllInSameFileOrAllTopLevel entry.2 ∧
      (∀ c, c ∈ entry.2 → ∃ loc, c.location = CommentLocation.fileLocation loc) ∧
      allCommentsHaveBackendId entry.2 ∧ allParentsInComments entry.2 ∧ commentRefsNodup entry.2 ∧
      parentsCreatedBefore entry.2 ∧
      (∀ c, c ∈ entry.2 → ∃ h' : comments₁.contains c.ref, (comments₁.get c.ref h').backendId.isSome))
    (bs : FileThreadsBootstrapState origState comments₁) : FileThreadsBootstrapState origState comments₁ :=
match l with
| [] => bs
| entry :: rest =>
  applyBaseThreads.go comments₁ origState rest (fun e he => hAll e (List.mem_cons_of_mem _ he))
    (let ⟨hFound, hSameLoc, hFileLoc, hBackend, hParents, hNodup, hBefore, hSubset⟩ := hAll entry List.mem_cons_self
     bs.applyBase entry.1 entry.2 hFound hSameLoc hFileLoc hBackend hParents hNodup hBefore hSubset)

/-- The `.current`-version counterpart of `applyBaseThreads.go`. -/
public def applyCurrentThreads.go (comments₁ : Std.HashMap CommentRef Comment)
    (origState : Std.HashMap ModifiedFileRef ModifiedFileState)
    (l : List (ModifiedFileRef × List Comment))
    (hAll : ∀ entry, entry ∈ l →
      origState.contains entry.1 ∧ commentsAllInSameFileOrAllTopLevel entry.2 ∧
      (∀ c, c ∈ entry.2 → ∃ loc, c.location = CommentLocation.fileLocation loc) ∧
      allCommentsHaveBackendId entry.2 ∧ allParentsInComments entry.2 ∧ commentRefsNodup entry.2 ∧
      parentsCreatedBefore entry.2 ∧
      (∀ c, c ∈ entry.2 → ∃ h' : comments₁.contains c.ref, (comments₁.get c.ref h').backendId.isSome))
    (bs : FileThreadsBootstrapState origState comments₁) : FileThreadsBootstrapState origState comments₁ :=
match l with
| [] => bs
| entry :: rest =>
  applyCurrentThreads.go comments₁ origState rest (fun e he => hAll e (List.mem_cons_of_mem _ he))
    (let ⟨hFound, hSameLoc, hFileLoc, hBackend, hParents, hNodup, hBefore, hSubset⟩ := hAll entry List.mem_cons_self
     bs.applyCurrent entry.1 entry.2 hFound hSameLoc hFileLoc hBackend hParents hNodup hBefore hSubset)

/-- The full batch of comments `addRemoteComments` bulk-loads: the top-level bucket plus every
file's base and current buckets, flattened into one list. `CommentManager.comments` is keyed by
`commentsByRef` of this list, so every published-ness obligation for any of the three buckets
ultimately reduces to a membership fact in `allComments`. -/
public def CommentBootstrapState.allComments (bootstrapState : CommentBootstrapState) : List Comment :=
  List.flatten [bootstrapState.topLevelComments, bootstrapState.baseComments.toList.flatMap Prod.snd, bootstrapState.currentComments.toList.flatMap Prod.snd]

private theorem CommentBootstrapState.mem_allComments_of_mem_topLevelComments
    (bootstrapState : CommentBootstrapState) (c : Comment) (hc : c ∈ bootstrapState.topLevelComments) :
    c ∈ bootstrapState.allComments := by
  simp only [CommentBootstrapState.allComments, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.mem_append]
  exact Or.inl hc

private theorem CommentBootstrapState.mem_allComments_of_mem_baseComments
    (bootstrapState : CommentBootstrapState) (entry : ModifiedFileRef × List Comment)
    (hentry : entry ∈ bootstrapState.baseComments.toList) (c : Comment) (hc : c ∈ entry.2) :
    c ∈ bootstrapState.allComments := by
  simp only [CommentBootstrapState.allComments, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.mem_append, List.mem_flatMap]
  exact Or.inr (Or.inl ⟨entry, hentry, hc⟩)

private theorem CommentBootstrapState.mem_allComments_of_mem_currentComments
    (bootstrapState : CommentBootstrapState) (entry : ModifiedFileRef × List Comment)
    (hentry : entry ∈ bootstrapState.currentComments.toList) (c : Comment) (hc : c ∈ entry.2) :
    c ∈ bootstrapState.allComments := by
  simp only [CommentBootstrapState.allComments, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.mem_append, List.mem_flatMap]
  exact Or.inr (Or.inr ⟨entry, hentry, hc⟩)

/-- Every comment across the batch's three buckets has a backend id, given each bucket already
satisfies `allCommentsHaveBackendId` on its own. -/
private theorem CommentBootstrapState.allComments_haveBackendId (bootstrapState : CommentBootstrapState)
    (hBackendTop : allCommentsHaveBackendId bootstrapState.topLevelComments)
    (hBackendBase : ∀ entry, entry ∈ bootstrapState.baseComments.toList → allCommentsHaveBackendId entry.2)
    (hBackendCurrent : ∀ entry, entry ∈ bootstrapState.currentComments.toList → allCommentsHaveBackendId entry.2) :
    ∀ c, c ∈ bootstrapState.allComments → c.backendId.isSome := by
  intro c hc
  simp only [CommentBootstrapState.allComments, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.mem_append, List.mem_flatMap] at hc
  rcases hc with hc | ⟨entry, hentry, hc⟩ | ⟨entry, hentry, hc⟩
  · exact hBackendTop c hc
  · exact hBackendBase entry hentry c hc
  · exact hBackendCurrent entry hentry c hc

/-- Once every comment in `allComments` is known to have a backend id, any sub-list `cs` of
`allComments` inherits `commentsByRef allComments`'s published-ness -- the fact each of
`FileThreadsBootstrapState.applyBase`/`.applyCurrent`'s `hSubset` argument needs. -/
private theorem allComments_hSubset {allComments : List Comment}
    (hAllBackend : ∀ c, c ∈ allComments → c.backendId.isSome) {cs : List Comment}
    (hsub : ∀ c, c ∈ cs → c ∈ allComments) :
    ∀ c, c ∈ cs → ∃ h' : (commentsByRef allComments).contains c.ref,
      ((commentsByRef allComments).get c.ref h').backendId.isSome :=
  fun c hc => ⟨commentsByRef_contains_of_mem allComments c (hsub c hc),
    commentsByRef_hPublished allComments hAllBackend c.ref _⟩

/-- Packages everything `applyBaseThreads.go` needs for `bootstrapState.baseComments.toList`, given
the file-tracked/backend/parents/nodup/before checks (`hBase`, from `addRemoteComments`'s validation)
and the global backend fact (`hAllBackend`, from `allComments_haveBackendId`). The
`commentsAllInSameFileOrAllTopLevel` and "file-located" facts come for free from
`bootstrapState.hBaseCommentsHaveBaseVersion`, since `groupComments` already guarantees every base
comment is file-located with version `.base`. -/
private theorem CommentBootstrapState.hAllBaseEntries (bootstrapState : CommentBootstrapState)
    {origState : Std.HashMap ModifiedFileRef ModifiedFileState}
    (hBase : ∀ entry, entry ∈ bootstrapState.baseComments.toList →
      origState.contains entry.1 ∧ allCommentsHaveBackendId entry.2 ∧ allParentsInComments entry.2 ∧
      commentRefsNodup entry.2 ∧ parentsCreatedBefore entry.2)
    (hAllBackend : ∀ c, c ∈ bootstrapState.allComments → c.backendId.isSome) :
    ∀ entry, entry ∈ bootstrapState.baseComments.toList →
      origState.contains entry.1 ∧ commentsAllInSameFileOrAllTopLevel entry.2 ∧
      (∀ c, c ∈ entry.2 → ∃ loc, c.location = CommentLocation.fileLocation loc) ∧
      allCommentsHaveBackendId entry.2 ∧ allParentsInComments entry.2 ∧ commentRefsNodup entry.2 ∧
      parentsCreatedBefore entry.2 ∧
      (∀ c, c ∈ entry.2 → ∃ h' : (commentsByRef bootstrapState.allComments).contains c.ref,
        ((commentsByRef bootstrapState.allComments).get c.ref h').backendId.isSome) :=
  fun entry hentry =>
    ⟨(hBase entry hentry).1,
      Or.inr (Or.inl (bootstrapState.hBaseCommentsHaveBaseVersion entry hentry)),
      fun c hc => (bootstrapState.hBaseCommentsHaveBaseVersion entry hentry c hc).imp (fun _ h => h.1),
      (hBase entry hentry).2.1, (hBase entry hentry).2.2.1, (hBase entry hentry).2.2.2.1,
      (hBase entry hentry).2.2.2.2,
      allComments_hSubset hAllBackend (bootstrapState.mem_allComments_of_mem_baseComments entry hentry)⟩

/-- The `.current`-version counterpart of `CommentBootstrapState.hAllBaseEntries`. -/
private theorem CommentBootstrapState.hAllCurrentEntries (bootstrapState : CommentBootstrapState)
    {origState : Std.HashMap ModifiedFileRef ModifiedFileState}
    (hCurrent : ∀ entry, entry ∈ bootstrapState.currentComments.toList →
      origState.contains entry.1 ∧ allCommentsHaveBackendId entry.2 ∧ allParentsInComments entry.2 ∧
      commentRefsNodup entry.2 ∧ parentsCreatedBefore entry.2)
    (hAllBackend : ∀ c, c ∈ bootstrapState.allComments → c.backendId.isSome) :
    ∀ entry, entry ∈ bootstrapState.currentComments.toList →
      origState.contains entry.1 ∧ commentsAllInSameFileOrAllTopLevel entry.2 ∧
      (∀ c, c ∈ entry.2 → ∃ loc, c.location = CommentLocation.fileLocation loc) ∧
      allCommentsHaveBackendId entry.2 ∧ allParentsInComments entry.2 ∧ commentRefsNodup entry.2 ∧
      parentsCreatedBefore entry.2 ∧
      (∀ c, c ∈ entry.2 → ∃ h' : (commentsByRef bootstrapState.allComments).contains c.ref,
        ((commentsByRef bootstrapState.allComments).get c.ref h').backendId.isSome) :=
  fun entry hentry =>
    ⟨(hCurrent entry hentry).1,
      Or.inr (Or.inr (bootstrapState.hCurrentCommentsHaveCurrentVersion entry hentry)),
      fun c hc => (bootstrapState.hCurrentCommentsHaveCurrentVersion entry hentry c hc).imp (fun _ h => h.1),
      (hCurrent entry hentry).2.1, (hCurrent entry hentry).2.2.1, (hCurrent entry hentry).2.2.2.1,
      (hCurrent entry hentry).2.2.2.2,
      allComments_hSubset hAllBackend (bootstrapState.mem_allComments_of_mem_currentComments entry hentry)⟩

/-- Builds the `CommentManager` for a validated comment batch: `comments` is keyed by `.ref` over
the whole batch (`allComments`), and `topLevelThreads` is assembled from the top-level bucket alone
(free of `hSameLocationTop`, since `groupComments` already guarantees every top-level comment is
actually top-level). -/
public def CommentBootstrapState.toCommentManager (bootstrapState : CommentBootstrapState)
    (hBackendTop : allCommentsHaveBackendId bootstrapState.topLevelComments)
    (hParentsTop : allParentsInComments bootstrapState.topLevelComments)
    (hNodupTop : commentRefsNodup bootstrapState.topLevelComments)
    (hBeforeTop : parentsCreatedBefore bootstrapState.topLevelComments)
    (hAllBackend : ∀ c, c ∈ bootstrapState.allComments → c.backendId.isSome) : CommentManager :=
  let hSameLocationTop : commentsAllInSameFileOrAllTopLevel bootstrapState.topLevelComments :=
    Or.inl bootstrapState.hTopLevelCommentsAreTopLevel
  { comments := commentsByRef bootstrapState.allComments,
    topLevelThreads := assembleCommentTrees bootstrapState.topLevelComments hSameLocationTop hBackendTop hParentsTop
      hNodupTop hBeforeTop,
    selectedComment := none,
    hSelectedCommentWellFormed := by simp,
    hCommentsKeyedByRef := commentsByRef_hCommentsKeyedByRef bootstrapState.allComments,
    hTopLevelThreadsAllTopLevel := assembleCommentTrees_locationRoots_isTopLevel bootstrapState.topLevelComments
      hSameLocationTop bootstrapState.hTopLevelCommentsAreTopLevel hBackendTop hParentsTop hNodupTop hBeforeTop,
    hTopLevelThreadsPublished := fun ref h' => by
      obtain ⟨c, hc, hcref⟩ := (assembleCommentTrees_commentTreeNodes_contains_iff bootstrapState.topLevelComments
        hSameLocationTop hBackendTop hParentsTop hNodupTop hBeforeTop ref).mp h'
      exact hcref ▸ allComments_hSubset hAllBackend (bootstrapState.mem_allComments_of_mem_topLevelComments) c hc }

/-- Builds the final `ModifiedFileManager` from a completed per-file thread-update fold:
`hConsistentState` transfers from `fileManager.resetCommentState`'s own (via `hSameContains`, since
the fold only ever replaces an already-tracked file's `ModifiedFileState`, never adds or removes
tracked files). -/
public def FileThreadsBootstrapState.toModifiedFileManager {comments₁ : Std.HashMap CommentRef Comment}
    (fileManager : ModifiedFileManager)
    (bs : FileThreadsBootstrapState fileManager.resetCommentState.state comments₁) : ModifiedFileManager :=
  { state := bs.state,
    modifiedFiles := fileManager.modifiedFiles,
    hConsistentState := fun mf => by
      rw [bs.hSameContains]
      exact fileManager.resetCommentState.hConsistentState mf }

/-- Bulk-loads a fresh batch of comments from the server, replacing whatever comment state was
there before.

Fails (leaving the state unchanged) if the server's batch doesn't satisfy the structural invariants
that we expect (see `assembleCommentTrees`). -/
public def addRemoteComments (s₀ : State) : Result (Except String Unit) :=
  match s₀.configuration.getRemoteConversations s₀.fileManager with
  | none => Result.mk (Except.ok ()) s₀
  | some comments =>
    let bootstrapState := groupComments comments
    if hTop : allCommentsHaveBackendId bootstrapState.topLevelComments ∧
        allParentsInComments bootstrapState.topLevelComments ∧
        commentRefsNodup bootstrapState.topLevelComments ∧
        parentsCreatedBefore bootstrapState.topLevelComments then
      let noCommentFileManager := s₀.fileManager.resetCommentState
      if hBase : ∀ entry, entry ∈ bootstrapState.baseComments.toList →
          noCommentFileManager.state.contains entry.1 ∧ allCommentsHaveBackendId entry.2 ∧
          allParentsInComments entry.2 ∧ commentRefsNodup entry.2 ∧ parentsCreatedBefore entry.2 then
        if hCurrent : ∀ entry, entry ∈ bootstrapState.currentComments.toList →
            noCommentFileManager.state.contains entry.1 ∧ allCommentsHaveBackendId entry.2 ∧
            allParentsInComments entry.2 ∧ commentRefsNodup entry.2 ∧ parentsCreatedBefore entry.2 then
          let ⟨hBackendTop, hParentsTop, hNodupTop, hBeforeTop⟩ := hTop
          let hAllBackend := bootstrapState.allComments_haveBackendId hBackendTop
            (fun entry hentry => (hBase entry hentry).2.1) (fun entry hentry => (hCurrent entry hentry).2.1)
          let initBS : FileThreadsBootstrapState noCommentFileManager.state
              (commentsByRef bootstrapState.allComments) :=
            { state := noCommentFileManager.state,
              hSameContains := fun _ => rfl,
              hPublished := s₀.fileManager.hFileThreadsPublished_resetCommentState
                (commentsByRef bootstrapState.allComments) }
          let bs1 := applyBaseThreads.go _ _ bootstrapState.baseComments.toList
            (bootstrapState.hAllBaseEntries hBase hAllBackend) initBS
          let bs2 := applyCurrentThreads.go _ _ bootstrapState.currentComments.toList
            (bootstrapState.hAllCurrentEntries hCurrent hAllBackend) bs1
          let s₁ : State :=
            { s₀ with
              commentBeingEdited := none,
              commentManager := bootstrapState.toCommentManager hBackendTop hParentsTop hNodupTop hBeforeTop
                hAllBackend,
              fileManager := bs2.toModifiedFileManager s₀.fileManager,
              hCommentBeingEditedWellFormed := by simp,
              hFileThreadsPublished := bs2.hPublished }
          Result.mk (Except.ok ()) s₁
        else Result.mk (Except.error "Received malformed comment data from the server") s₀
      else Result.mk (Except.error "Received malformed comment data from the server") s₀
    else Result.mk (Except.error "Received malformed comment data from the server") s₀

/-- Finalizes publishing a top-level being-edited comment: threads `comment₂` into
`s₀.commentManager.topLevelThreads` and assembles the resulting `State`. `comments₁` (the new
`CommentManager.comments`) is recomputed from `comment₀`/`comment₂`/`href2` rather than taken as a
parameter, since it must stay *definitionally* `s₀.commentManager.comments.insert comment₀.ref
comment₂` for the proofs below to typecheck -- an opaque parameter would lose that. -/
public def completeCommentWithContent.finalizeTopLevel (s₀ : State) (comment₀ comment₂ : Comment)
    (hloc : comment₂.location = CommentLocation.topLevel) (hHasBackendId : comment₂.backendId.isSome)
    (href2 : comment₂.ref = comment₀.ref) (hFresh0 : ¬ s₀.commentManager.comments.contains comment₀.ref)
    (hparent2 : ∀ parentId, comment₂.parent = some parentId →
      parentId ∈ s₀.commentManager.topLevelThreads.serverCommentIds)
    (hFileThreadsPublished₁ : ∀ modifiedFileRef (h : s₀.fileManager.state.contains modifiedFileRef),
      (∀ ref (_hc : (s₀.fileManager.state.get modifiedFileRef h).baseThreads.commentTreeNodes.contains ref),
        ∃ h' : (s₀.commentManager.comments.insert comment₀.ref comment₂).contains ref,
          ((s₀.commentManager.comments.insert comment₀.ref comment₂).get ref h').backendId.isSome) ∧
      (∀ ref (_hc : (s₀.fileManager.state.get modifiedFileRef h).currentThreads.commentTreeNodes.contains ref),
        ∃ h' : (s₀.commentManager.comments.insert comment₀.ref comment₂).contains ref,
          ((s₀.commentManager.comments.insert comment₀.ref comment₂).get ref h').backendId.isSome)) :
    State :=
  let comments₁ := s₀.commentManager.comments.insert comment₀.ref comment₂
  have hCommentsKeyedByRef₁ : ∀ ref (h : comments₁.contains ref), (comments₁.get ref h).ref = ref :=
    s₀.commentManager.hCommentsKeyedByRef_insert comment₀.ref comment₂ href2
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
  { s₀ with
    commentBeingEdited := none,
    commentManager := commentManager₁,
    hCommentBeingEditedWellFormed := by simp,
    hFileThreadsPublished := hFileThreadsPublished₁ }

/-- Selects whichever of `baseThreads` / `currentThreads` `version` names -- the shared accessor
that lets `completeCommentWithContent.finalizeFileScoped` treat the `.base` and `.current` cases
uniformly. -/
public def ModifiedFileState.threadsFor (mfs : ModifiedFileState) (v : FileVersion) : CommentThreads :=
  match v with
  | .base => mfs.baseThreads
  | .current => mfs.currentThreads

/-- The `hBaseThreadsFileScoped` / `hCurrentThreadsFileScoped` invariant, selected by `version`. -/
private theorem ModifiedFileState.hThreadsFileScoped (mfs : ModifiedFileState) (version : FileVersion) :
    ∀ loc, loc ∈ (mfs.threadsFor version).locationRoots.keys → loc.isTopLevel = false := by
  cases version with
  | base => exact mfs.hBaseThreadsFileScoped
  | current => exact mfs.hCurrentThreadsFileScoped

/-- `locationScope_of_base` / `locationScope_of_current`, selected by `version`. -/
private theorem ModifiedFileState.locationScopeFor (mfs : ModifiedFileState) (version : FileVersion)
    {location : CommentLocation} (hloc : location.asThreadLocation.isTopLevel = false) :
    ∀ loc', loc' ∈ (mfs.threadsFor version).locationRoots.keys →
      loc'.isTopLevel = location.asThreadLocation.isTopLevel := by
  cases version with
  | base => exact mfs.locationScope_of_base hloc
  | current => exact mfs.locationScope_of_current hloc

/-- `State.notMem_baseThreads_of_unpublished` / `notMem_currentThreads_of_unpublished`, selected by
`version`. -/
private theorem State.notMem_threadsFor_of_unpublished (s : State) {ref : CommentRef}
    (hFresh : ¬ s.commentManager.comments.contains ref) {fileRef : ModifiedFileRef}
    (h : s.fileManager.state.contains fileRef) (version : FileVersion) :
    ref ∉ ((s.fileManager.state.get fileRef h).threadsFor version).commentTreeNodes := by
  cases version with
  | base => exact s.notMem_baseThreads_of_unpublished hFresh h
  | current => exact s.notMem_currentThreads_of_unpublished hFresh h

/-- Rebuilds `mfs` with `threadsFor version` replaced by `newThreads` (and the matching
`hThreadsFileScoped` obligation discharged by `hFileScoped`), leaving the other version's threads
untouched. The setter counterpart of `threadsFor`. -/
public def ModifiedFileState.withThreadsFor (mfs : ModifiedFileState) (version : FileVersion)
    (newThreads : CommentThreads)
    (hFileScoped : ∀ loc, loc ∈ newThreads.locationRoots.keys → loc.isTopLevel = false) : ModifiedFileState :=
  match version with
  | .base =>
    { mfs with
      baseThreads := newThreads,
      selectedComment := none,
      hSelectedCommentWellFormed := by simp,
      hBaseThreadsFileScoped := hFileScoped }
  | .current =>
    { mfs with
      currentThreads := newThreads,
      selectedComment := none,
      hSelectedCommentWellFormed := by simp,
      hCurrentThreadsFileScoped := hFileScoped }

/-- Finalizes publishing a file-scoped being-edited comment into whichever of a file's `baseThreads`
/ `currentThreads` `version` names, leaving the other untouched, and assembles the resulting
`State`. Generalizes what were previously separate `finalizeBase` / `finalizeCurrent` defs: every
step through `hFileThreadsPublished₂` is version-generic via `threadsFor` / `hThreadsFileScoped` /
`withThreadsFor` / `locationScopeFor` / `notMem_threadsFor_of_unpublished`, except the final call,
which still has to name `State.hFileThreadsPublished_insert_base` / `_insert_current` explicitly
since those remain separate theorems (each asserting the *other* field is unchanged in a way that's
tied to the concrete field name, not expressible through `threadsFor` alone). `comments₁` is
recomputed rather than taken as a parameter, for the same reason as in `finalizeTopLevel`. -/
def completeCommentWithContent.finalizeFileScoped (s₀ : State) (comment₀ comment₂ : Comment)
    {serverId : ServerId} (fileRef : ModifiedFileRef) (modifiedFileState : ModifiedFileState)
    (hOldContainsFileRef : s₀.fileManager.state.contains fileRef)
    (hgetval : s₀.fileManager.state.get fileRef hOldContainsFileRef = modifiedFileState)
    (hHasBackendId : comment₂.backendId.isSome) (href2 : comment₂.ref = comment₀.ref)
    (hbackendId2 : comment₂.backendId = some serverId)
    (hFresh0 : ¬ s₀.commentManager.comments.contains comment₀.ref)
    (version : FileVersion)
    (hparent : ∀ parentId, comment₂.parent = some parentId →
      parentId ∈ (modifiedFileState.threadsFor version).serverCommentIds)
    (hcommentTop : comment₂.location.asThreadLocation.isTopLevel = false)
    (hTopLevelThreadsPublished₁ : ∀ ref' (_h : s₀.commentManager.topLevelThreads.commentTreeNodes.contains ref'),
      ∃ h' : (s₀.commentManager.comments.insert comment₀.ref comment₂).contains ref',
        ((s₀.commentManager.comments.insert comment₀.ref comment₂).get ref' h').backendId.isSome) :
    State :=
  let comments₁ := s₀.commentManager.comments.insert comment₀.ref comment₂
  have hCommentsKeyedByRef₁ : ∀ ref (h : comments₁.contains ref), (comments₁.get ref h).ref = ref :=
    s₀.commentManager.hCommentsKeyedByRef_insert comment₀.ref comment₂ href2
  have hRefFresh : comment₂.ref ∉ (modifiedFileState.threadsFor version).commentTreeNodes := by
    rw [href2, ← hgetval]
    exact s₀.notMem_threadsFor_of_unpublished hFresh0 hOldContainsFileRef version
  have hLocationScope := modifiedFileState.locationScopeFor version hcommentTop
  have hParentThreadRegistered :
      ∀ parentId (h : parentId ∈ (modifiedFileState.threadsFor version).serverCommentIds),
        comment₂.parent = some parentId →
          (modifiedFileState.threadsFor version).serverCommentIds.get parentId h ∈
            (modifiedFileState.threadsFor version).commentTreeNodes :=
    fun parentId h _ => (modifiedFileState.threadsFor version).hParentThreadRegistered_mem parentId h
  let newThreads := addCommentToThread (modifiedFileState.threadsFor version) comment₂
    hHasBackendId hparent hParentThreadRegistered hRefFresh hLocationScope
  have hFileScoped₁ : ∀ loc', loc' ∈ newThreads.locationRoots.keys → loc'.isTopLevel = false :=
    addCommentToThread_locationRoots_isTopLevel (modifiedFileState.threadsFor version) comment₂
      hHasBackendId hparent hParentThreadRegistered hRefFresh hLocationScope false
      (modifiedFileState.hThreadsFileScoped version) hcommentTop
  let commentManager₁ : CommentManager :=
    { s₀.commentManager with
      comments := comments₁,
      hCommentsKeyedByRef := hCommentsKeyedByRef₁,
      hTopLevelThreadsPublished := hTopLevelThreadsPublished₁ }
  have hNewThreadsContains : ∀ ref, newThreads.commentTreeNodes.contains ref ↔
      (modifiedFileState.threadsFor version).commentTreeNodes.contains ref ∨ ref = comment₂.ref :=
    addCommentToThread_commentTreeNodes_contains_iff (modifiedFileState.threadsFor version) comment₂
      hHasBackendId hparent hParentThreadRegistered hRefFresh hLocationScope
  -- The remaining steps (building `newFileState`, calling `State.hFileThreadsPublished_insert_base` /
  -- `_insert_current`) genuinely need `version` to be the literal `.base` / `.current` tag: those two
  -- theorems each assert that the *other* field is unchanged, tied to the concrete field name, not
  -- expressible through `threadsFor` alone. Matching here (rather than a plain `cases version` inside
  -- a later tactic block) is what lets the trailing `rfl`s below actually typecheck.
  match version, hNewThreadsContains with
  | .base, hNewThreadsContains =>
    let newFileState := modifiedFileState.withThreadsFor .base newThreads hFileScoped₁
    let newState := s₀.fileManager.state.insert fileRef newFileState
    have hFileThreadsPublished₂ := s₀.hFileThreadsPublished_insert_base (newFileState := newFileState)
      (newState := newState) (newComments := comments₁) hOldContainsFileRef hgetval hFresh0 href2 hbackendId2
      hNewThreadsContains rfl rfl rfl rfl
    have hConsistentState₁ := s₀.fileManager.hConsistentState_insert hOldContainsFileRef newFileState
    let fileManager₁ : ModifiedFileManager :=
      { s₀.fileManager with state := newState, hConsistentState := hConsistentState₁ }
    { s₀ with
      commentBeingEdited := none,
      commentManager := commentManager₁,
      fileManager := fileManager₁,
      hCommentBeingEditedWellFormed := by simp,
      hFileThreadsPublished := hFileThreadsPublished₂ }
  | .current, hNewThreadsContains =>
    let newFileState := modifiedFileState.withThreadsFor .current newThreads hFileScoped₁
    let newState := s₀.fileManager.state.insert fileRef newFileState
    have hFileThreadsPublished₂ := s₀.hFileThreadsPublished_insert_current (newFileState := newFileState)
      (newState := newState) (newComments := comments₁) hOldContainsFileRef hgetval hFresh0 href2 hbackendId2
      hNewThreadsContains rfl rfl rfl rfl
    have hConsistentState₁ := s₀.fileManager.hConsistentState_insert hOldContainsFileRef newFileState
    let fileManager₁ : ModifiedFileManager :=
      { s₀.fileManager with state := newState, hConsistentState := hConsistentState₁ }
    { s₀ with
      commentBeingEdited := none,
      commentManager := commentManager₁,
      fileManager := fileManager₁,
      hCommentBeingEditedWellFormed := by simp,
      hFileThreadsPublished := hFileThreadsPublished₂ }

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

        -- Inserting the (freshly-published) being-edited comment into `comments` can't disturb any
        -- other ref's published status: it either was already there and is untouched, or it *is*
        -- `comment₀.ref`, which was fresh (unregistered) and so can't have been the ref some other
        -- invariant already certified as published.
        have hPreservePublished := s₀.commentManager.preservePublished_insert hFresh0 comment₂

        have hFileThreadsPublished₁ := s₀.hFileThreadsPublished_of_preserve hPreservePublished

        match hloc : comment₀.location with
        | .topLevel =>
          have hparent2 : ∀ parentId, comment₂.parent = some parentId →
              parentId ∈ s₀.commentManager.topLevelThreads.serverCommentIds := by
            intro parentId hp
            have hres := hparent0 parentId hp
            rw [hloc] at hres
            exact hres
          Result.mk (Except.ok comment₂) (completeCommentWithContent.finalizeTopLevel s₀ comment₀ comment₂
            hloc hHasBackendId href2 hFresh0 hparent2 hFileThreadsPublished₁)
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

            Result.mk (Except.ok comment₂) (completeCommentWithContent.finalizeFileScoped s₀ comment₀ comment₂
              fileRef modifiedFileState hOldContainsFileRef hgetval hHasBackendId href2 hbackendId2 hFresh0
              loc.version hparentFile hcommentTop hTopLevelThreadsPublished₁)

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
