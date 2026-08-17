import Std
import Init.System
import Init.Data.List.Sort

namespace Lgtm

private structure Tree (α : Type) where
  value : α
  children : List (Tree α)


def Tree.addChild (t : Tree α) (child : Tree α) : Tree α :=
  ⟨t.value, child :: t.children⟩

/-- A reference that can be mapped to (mutable) comment contents -/
structure CommentRef where
  /-- A unique identifier

  These are only unique within a session.
  -/
  id : String
  deriving Inhabited, Hashable, DecidableEq

structure FileRef where
  path : String
  deriving Hashable, BEq

inductive FileVersion where
  | base
  | current
  deriving Hashable, BEq

structure CommentFileLocation where
  version : FileVersion
  fileRef : FileRef
  startLine : Nat
  startColumn : Nat
  endLine : Nat
  endColumn : Nat
  deriving Hashable, BEq

inductive CommentLocation where
  | fileLocation : CommentFileLocation → CommentLocation
  | topLevel : CommentLocation
  deriving Hashable, BEq

private def CommentLocation.isTopLevel : CommentLocation → Bool
| .topLevel => true
| .fileLocation _ => false

structure ServerId where
  id : String
  deriving Inhabited, Hashable, BEq

/-- The actual contents of a comment.

This is separated out from references, as references often need to be hashed
or compared for equality, which is expensive if the reference actually includes
all of the comment data. -/
structure Comment where
  /-- The unique id assigned to this comment.

  For new comments this is a gensym.  For comments fetched from the server, it
  is the server id. -/
  ref : CommentRef
  /-- The id of the comment on the server side.  This is only populated for
  comments fetched from the server and for comments that are sent to the server
  (even if they are unpublished) -/
  backendId : Option ServerId
  /-- The location of the comment.

  This is none for top-level comments. -/
  location : Option CommentLocation
  isPublished : Bool
  author : String
  createdTimestamp : Nat
  updatedTimestamp : Nat
  /-- The id of the parent comment, if any.

  Parent comments must be published, so this must exist if there is a reply being created. -/
  parent : Option ServerId
  /-- The id to reply to if replying to this comment.

  This might not be the server id of this comment if the server only tracks linear
  discussions instead of structured threads.  This is none if the comment is unpublished. -/
  replyToId : Option ServerId

  /-- The content of the comment. -/
  content : String
  deriving Inhabited

def Comment.isPersistedToServer (c : Comment) : Bool := c.backendId.isSome

-- FIXME: Should this be a tree of comments instead? There should be no harm (it is fine in the current implementation)
--
-- Downside: The current implementation acts more like IORefs everywhere.  Mutations to comments here would
-- not work or be visible.  Therefore, keeping all of the comments actually in the manager instead is probably
-- the better design
abbrev CommentThread := Tree CommentRef

instance : Inhabited (Tree CommentRef) where
  default := ⟨default, []⟩

/-- Locations of threads for rendering purposes.

These locations are less precise than the comment locations and are just
used for the renderer to group threads appropriately. -/
private inductive ThreadLocation where
| topLevel
| lineNumber : Nat → ThreadLocation
deriving Hashable, Ord, DecidableEq

private def ThreadLocation.isTopLevel : ThreadLocation → Bool
| .topLevel => true
| .lineNumber _ => false

/-- The collected threads for a scope (file version or top-level). -/
private structure CommentThreads where
  /-- The tree node for each comment. -/
  commentTreeNodes : Std.HashMap CommentRef CommentThread

  serverCommentIds : Std.HashMap ServerId CommentRef

  locationRoots : Std.HashMap ThreadLocation (List CommentRef)

  /-- Invariant: Either there is one location that is top or there are no locations that are top -/
  hLocationsConsistent : (∀ loc, loc ∈ locationRoots.keys → loc.isTopLevel ∧ locationRoots.size = 1) ∨ (∀ loc, loc ∈ locationRoots.keys → ¬ loc.isTopLevel)

  /-- All referenced comments have an associated node -/
  hHasNodeForComment : ∀ loc threadRoots, (loc, threadRoots) ∈ locationRoots.toList →
    ∀ ref, ref ∈ threadRoots → commentTreeNodes.contains ref

  hAllCommentTreeNodesAreLive : ∀ commentRef, commentRef ∈ commentTreeNodes.keys → ∃ threadsList, threadsList ∈ locationRoots.values ∧ commentRef ∈ threadsList

private def CommentThreads.empty : CommentThreads := ⟨Std.HashMap.emptyWithCapacity, Std.HashMap.emptyWithCapacity, Std.HashMap.emptyWithCapacity, by simp, by simp, by simp⟩

/-- Whether there are any threads to show.

Note: this is based on `locationRoots` (what's actually reachable/displayable), not
`commentTreeNodes` (which can contain tree nodes that no location references). -/
private def CommentThreads.isEmpty (threads : CommentThreads) : Bool :=
  threads.locationRoots.toList.all (fun p => p.2.isEmpty)

private structure CommentManager where
  comments : Std.HashMap CommentRef Comment
  topLevelThreads : CommentThreads

private def CommentManager.empty : CommentManager := ⟨Std.HashMap.emptyWithCapacity, CommentThreads.empty⟩

private def CommentManager.get (manager : CommentManager) (ref : CommentRef) : Comment :=
  manager.comments[ref]!

/-- Extract an alist of threads grouped by location.

The list is sorted by location.  Each list at a given location is sorted by comment timestamp.
The comment manager is required to get access to those timestamps. -/
private def CommentThreads.asAlist (threads : CommentThreads) (manager : CommentManager) : List (ThreadLocation × List CommentThread) :=
  let unsorted := threads.locationRoots.toList.attach.map (λ ⟨(loc, threadRoots), hpair⟩ =>
    let commentThreads := threadRoots.attach.map (λ ⟨commentRef, href⟩ =>
      let hMember := Std.HashMap.mem_iff_contains.mpr (threads.hHasNodeForComment loc threadRoots hpair commentRef href)
      threads.commentTreeNodes.get commentRef hMember)
    let sortByComparison := λ t1 t2 => (compare (manager.get t1.value).createdTimestamp (manager.get t2.value).createdTimestamp).isLE
    let sortedThreads := List.mergeSort commentThreads sortByComparison
    (loc, sortedThreads))
  unsorted.mergeSort (λ p1 p2 => (compare p1.fst p2.fst).isLE)

def hasConsistentLocationsPredicate (locations : List ThreadLocation) : Prop :=
  (∀ loc, loc ∈ locations → loc.isTopLevel) ∨ (∀ loc, loc ∈ locations → !loc.isTopLevel)

theorem CommentThreads.asAlist.hasConsistentLocations (threads : CommentThreads) (manager : CommentManager) :
  hasConsistentLocationsPredicate (List.map Prod.fst (threads.asAlist manager)) := by
  have hmem : ∀ loc, loc ∈ List.map Prod.fst (threads.asAlist manager) → loc ∈ threads.locationRoots.keys := by
    intro loc hloc
    unfold CommentThreads.asAlist at hloc
    simp only [List.mem_map, List.mem_mergeSort, List.mem_attach, true_and] at hloc
    obtain ⟨a, ⟨a1, heq1⟩, heq2⟩ := hloc
    have hloceq : loc = a1.1.fst := by rw [← heq2, ← heq1]
    rw [hloceq, ← Std.HashMap.map_fst_toList_eq_keys]
    exact List.mem_map.mpr ⟨a1.1, a1.2, rfl⟩
  rcases threads.hLocationsConsistent with hc | hc
  · exact Or.inl (fun loc hloc => (hc loc (hmem loc hloc)).1)
  · exact Or.inr (fun loc hloc => by simpa using hc loc (hmem loc hloc))

private def listIsSortedPredicate [Ord α] (values : List α) : Prop :=
  match values with
  | [] => True
  | v :: rest => rest.all (λ other => (compare v other).isLE) ∧ listIsSortedPredicate rest

private def ThreadLocation.le (a b : ThreadLocation) : Bool := (compare a b).isLE

private theorem ThreadLocation.le_trans : ∀ (a b c : ThreadLocation), le a b → le b c → le a c := by
  intro a b c
  unfold le compare instOrdThreadLocation instOrdThreadLocation.ord
  rcases a <;> rcases b <;> rcases c <;> simp [Nat.isLE_compare] <;> omega

private theorem ThreadLocation.le_total : ∀ (a b : ThreadLocation), le a b || le b a := by
  intro a b
  unfold le compare instOrdThreadLocation instOrdThreadLocation.ord
  rcases a <;> rcases b <;> simp [Nat.isLE_compare] <;> omega

private theorem listIsSortedPredicate_iff_pairwise {α} [Ord α] (l : List α) :
    listIsSortedPredicate l ↔ l.Pairwise (fun a b => (compare a b).isLE = true) := by
  induction l with
  | nil => simp [listIsSortedPredicate]
  | cons a l ih => simp [listIsSortedPredicate, ih]

theorem CommentThreads.asAlist.isSortedByLocation (threads : CommentThreads) (manager : CommentManager) :
  listIsSortedPredicate (List.map Prod.fst (threads.asAlist manager)) := by
  unfold CommentThreads.asAlist
  rw [List.map_mergeSort (s := ThreadLocation.le) (by intro a _ b _; rfl)]
  rw [listIsSortedPredicate_iff_pairwise]
  exact List.pairwise_mergeSort ThreadLocation.le_trans ThreadLocation.le_total _

private theorem nat_compareLE_trans : ∀ (a b c : Nat), (compare a b).isLE → (compare b c).isLE → (compare a c).isLE := by
  intro a b c
  simp only [Nat.isLE_compare]
  omega

private theorem nat_compareLE_total : ∀ (a b : Nat), (compare a b).isLE || (compare b a).isLE := by
  intro a b
  simp only [Nat.isLE_compare, Bool.or_eq_true]
  omega

theorem CommentThreads.asAlist.threadLocationsSortedByTimestamp (threads : CommentThreads) (manager : CommentManager) :
  ∀ threadList, threadList ∈ (List.map Prod.snd (threads.asAlist manager)) →
       listIsSortedPredicate (List.map (λ commentRef => (manager.get commentRef.value).createdTimestamp) threadList) := by
  intro threadList hthreadList
  unfold CommentThreads.asAlist at hthreadList
  simp only [List.mem_map, List.mem_mergeSort, List.mem_attach, true_and] at hthreadList
  obtain ⟨a, ⟨⟨⟨loc, threadRoots⟩, hpair⟩, heq1⟩, heq2⟩ := hthreadList
  have hthreadListEq : threadList =
      List.mergeSort
        (List.map (fun x => threads.commentTreeNodes.get x.val
            (Std.HashMap.mem_iff_contains.mpr (threads.hHasNodeForComment loc threadRoots hpair x.val x.2)))
          threadRoots.attach)
        (fun t1 t2 => (compare (manager.get t1.value).createdTimestamp (manager.get t2.value).createdTimestamp).isLE) := by
    rw [← heq2, ← heq1]
  rw [listIsSortedPredicate_iff_pairwise, List.pairwise_map, hthreadListEq]
  refine (List.pairwise_mergeSort ?_ ?_ _).imp (fun {x y} h => ?_)
  · intro t1 t2 t3 h1 h2
    exact nat_compareLE_trans _ _ _ h1 h2
  · intro t1 t2
    exact nat_compareLE_total _ _
  · exact h


/-- Return the threads in sorted order. -/
private def CommentThreads.toThreadsOrdered (threads : CommentThreads) (manager : CommentManager) : List CommentThread :=
  List.flatMap (λ p => Prod.snd p) (threads.asAlist manager)

/-- Each group of threads that `toThreadsOrdered` concatenates in (i.e. each location's thread
list from `asAlist`) occurs as a contiguous run in the result, and that run is sorted by
timestamp. -/
theorem CommentThreads.toThreadsOrdered.groupsAreSorted (threads : CommentThreads) (manager : CommentManager) :
  ∀ threadList, threadList ∈ (List.map Prod.snd (threads.asAlist manager)) →
    threadList.IsInfix (threads.toThreadsOrdered manager) ∧
    listIsSortedPredicate (List.map (λ thread => (manager.get thread.value).createdTimestamp) threadList) := by
  intro threadList hthreadList
  refine ⟨?_, CommentThreads.asAlist.threadLocationsSortedByTimestamp threads manager threadList hthreadList⟩
  obtain ⟨p, hp_mem, hp_eq⟩ := List.mem_map.mp hthreadList
  obtain ⟨s, t, hst⟩ := List.append_of_mem hp_mem
  refine ⟨List.flatMap Prod.snd s, List.flatMap Prod.snd t, ?_⟩
  unfold CommentThreads.toThreadsOrdered
  rw [hst, List.flatMap_append, List.flatMap_cons, hp_eq, List.append_assoc]

/-- The comment selected in the file review UI. -/
structure SelectedComment where
  version : FileVersion
  thread : CommentThread
  comment : CommentRef

/--
Given a collection of threads and a selection, return the next thread to select linearly.

The VERSION is included because the user can switch files; as there is only one global selection,
if the user selects the next comment in a different file, the whole selection resets.

The linear order is as established in the ordering defined by CommentThreads.

Note: It would be nice to keep the association between the selection and the threads objects it references.  Future work.
-/
private def CommentThreads.nextThread (threads : CommentThreads) (manager : CommentManager) (version : FileVersion) (selection : SelectedComment) : Option SelectedComment :=
  let orderedThreads := threads.toThreadsOrdered manager
  match version == selection.version, orderedThreads with
  | false, [] => none
  | false, firstThread :: _ => some ⟨version, firstThread, firstThread.value⟩
  | true, _ =>
    match orderedThreads.findIdx? (·.value == selection.thread.value) with
    | none => none
    | some curIdx =>
      /- This should be provable because if we found the thread in the list, the list cannot be empty -/
      let nextIdx := Nat.min (curIdx + 1) (orderedThreads.length - 1)
      let nextThread := orderedThreads[nextIdx]!
      some ⟨version, nextThread, nextThread.value⟩

private theorem CommentThreads.toThreadsOrdered.eq_nil_of_isEmpty (threads : CommentThreads) (manager : CommentManager)
    (hEmpty : threads.isEmpty) : threads.toThreadsOrdered manager = [] := by
  have hThreadRootsEmpty : ∀ loc threadRoots, (loc, threadRoots) ∈ threads.locationRoots.toList → threadRoots = [] := by
    intro loc threadRoots hpair
    unfold CommentThreads.isEmpty at hEmpty
    rw [List.all_eq_true] at hEmpty
    simpa using hEmpty (loc, threadRoots) hpair
  unfold CommentThreads.toThreadsOrdered CommentThreads.asAlist
  rw [List.flatMap_eq_nil_iff]
  intro p hp
  simp only [List.mem_mergeSort, List.mem_map, List.mem_attach, true_and] at hp
  obtain ⟨⟨⟨loc, threadRoots⟩, hpair⟩, heq⟩ := hp
  have hRootsEmpty := hThreadRootsEmpty loc threadRoots hpair
  subst hRootsEmpty
  rw [← heq]
  simp

theorem CommentThreads.nextThread.noSelectionForEmptyFile (threads : CommentThreads) (manager : CommentManager) (version : FileVersion) (selection : SelectedComment) :
  version ≠ selection.version ∧ threads.isEmpty → threads.nextThread manager version selection = none := by
  rintro ⟨hverne, hEmpty⟩
  have hVerNe : (version == selection.version) = false := by
    obtain ⟨sv, sthread, scomment⟩ := selection
    cases version <;> cases sv <;> simp_all <;> rfl
  unfold CommentThreads.nextThread
  rw [CommentThreads.toThreadsOrdered.eq_nil_of_isEmpty threads manager hEmpty]
  simp [hVerNe]

/-- Every location's thread list contributes a matching-length group to `asAlist`'s output. -/
private theorem CommentThreads.asAlist.mem_of_locationRoots (threads : CommentThreads) (manager : CommentManager) :
    ∀ loc threadRoots, (loc, threadRoots) ∈ threads.locationRoots.toList →
      ∃ sortedThreads, (loc, sortedThreads) ∈ threads.asAlist manager ∧ sortedThreads.length = threadRoots.length := by
  intro loc threadRoots hpair
  unfold CommentThreads.asAlist
  refine ⟨_, List.mem_mergeSort.mpr (List.mem_map.mpr ⟨⟨(loc, threadRoots), hpair⟩, List.mem_attach _ _, rfl⟩), ?_⟩
  simp

private theorem CommentThreads.toThreadsOrdered.isEmpty_of_eq_nil (threads : CommentThreads) (manager : CommentManager)
    (hNil : threads.toThreadsOrdered manager = []) : threads.isEmpty := by
  unfold CommentThreads.isEmpty
  rw [List.all_eq_true]
  rintro ⟨loc, threadRoots⟩ hpair
  obtain ⟨sortedThreads, hmem, hlen⟩ := CommentThreads.asAlist.mem_of_locationRoots threads manager loc threadRoots hpair
  unfold CommentThreads.toThreadsOrdered at hNil
  rw [List.flatMap_eq_nil_iff] at hNil
  have hsnil := hNil (loc, sortedThreads) hmem
  simp only at hsnil
  rw [hsnil, List.length_nil] at hlen
  simp only [List.isEmpty_iff_length_eq_zero]
  omega

private theorem CommentThreads.toThreadsOrdered.ne_nil_of_not_isEmpty (threads : CommentThreads) (manager : CommentManager)
    (hNonEmpty : ¬ threads.isEmpty) : threads.toThreadsOrdered manager ≠ [] := by
  intro hNil
  exact hNonEmpty (CommentThreads.toThreadsOrdered.isEmpty_of_eq_nil threads manager hNil)

theorem CommentThreads.nextThread.selectFirstForDifferentFile (threads : CommentThreads) (manager : CommentManager) (version : FileVersion) (selection : SelectedComment) :
  version ≠ selection.version ∧ ¬ threads.isEmpty →
    ∃ thread, (threads.toThreadsOrdered manager).head? = some thread ∧
              threads.nextThread manager version selection = some ⟨version, thread, thread.value⟩ := by
  rintro ⟨hverne, hNonEmpty⟩
  have hVerNe : (version == selection.version) = false := by
    obtain ⟨sv, sthread, scomment⟩ := selection
    cases version <;> cases sv <;> simp_all <;> rfl
  have hNeNil : threads.toThreadsOrdered manager ≠ [] :=
    CommentThreads.toThreadsOrdered.ne_nil_of_not_isEmpty threads manager hNonEmpty
  unfold CommentThreads.nextThread
  match hmatch : threads.toThreadsOrdered manager with
  | [] => exact absurd hmatch hNeNil
  | firstThread :: rest =>
    exact ⟨firstThread, by simp, by simp [hVerNe]⟩

/- theorem CommentThreads.nextThread.saturateIfLastThreadSelected (threads : CommentThreads) (manager : CommentManager) (version : FileVersion) (selection : SelectedComment) :
 -   version = selection.version ∧ ∃ idx, -/

/-- A hash of a git revision -/
private structure GitRevision where
  hash : String
  deriving Hashable, DecidableEq

private structure RepositoryRef where
  /-- The name of the repository -/
  name : String
  /-- The path of the repository on disk -/
  path : System.FilePath
  /-- The revision that the changeset will be applied to in the repository -/
  baseRevision : GitRevision
  deriving Hashable, DecidableEq

structure Repository where
  /-- The name of the repository -/
  name : String
  /-- The path of the repository on disk -/
  path : System.FilePath
  /-- The revision that the changeset will be applied to in the repository -/
  baseRevision : GitRevision
  /-- The list of commits and their commit messages for the changeset

  The strings are the commit messages corresponding to each revision.
  -/
  commits : List (GitRevision × String)

inductive ModificationType where
| modified
| added
| deleted
| renamed
| copied
| typechange
deriving Hashable, DecidableEq

private structure ModifiedFileRef where
  repositoryRef : RepositoryRef
  modificationType : ModificationType
  baseFileName : String
  baseFileHash : GitRevision
  currentFileName : String
  currentFileHash : GitRevision
  deriving Hashable, DecidableEq

/--
The mutable state for a file that can be reviewed.

Note: This used to track the last position in each file but that wasn't used.
-/
private structure ModifiedFileState where
  ref : ModifiedFileRef
  fileRef : FileRef
  selectedComment : Option SelectedComment
  baseThreads : CommentThreads
  currentThreads : CommentThreads

private structure ModifiedFileManager where
  state : Std.HashMap ModifiedFileRef ModifiedFileState
  /-- The files affected by the change in a server-defined order.  This is stored
  separately to preserve that order, which would be lost with only the hash map.

  Invariant: Each one of these has an entry in `state`. -/
  modifiedFiles : List ModifiedFileRef

  hConsistentState : ∀ modifiedFile, modifiedFile ∈ modifiedFiles → state.contains modifiedFile

private def ModifiedFileManager.resetCommentState (fileManager : ModifiedFileManager) : ModifiedFileManager :=
  let updatedState := fileManager.state.map (fun modifiedFileRef fileState =>
    {fileState with selectedComment := none,
                    baseThreads := CommentThreads.empty,
                    currentThreads := CommentThreads.empty})
  have hConsistent : ∀ modifiedFile, modifiedFile ∈ fileManager.modifiedFiles → updatedState.contains modifiedFile := by
    intro modifiedFile hmem
    simp only [updatedState, Std.HashMap.contains_map]
    exact fileManager.hConsistentState modifiedFile hmem
  { fileManager with state := updatedState, hConsistentState := hConsistent }

/-- This would ideally be an inductive, but different servers can provide different statuses.  We just
take what they give us. -/
structure ChangesetStatus where
  status : String

structure Configuration where
  user : String
  changesetId : String
  repositories : List Repository
  /-- The author of the changeset -/
  author : String
  createdAt : Nat
  status : ChangesetStatus
  changesetUrl : String
  changesetTitle : String
  changesetDescription : String

private structure State where
  configuration : Configuration
  activeReviewedFile : Option ModifiedFileRef
  commentBeingEdited : Option CommentRef
  commentManager : CommentManager
  fileManager : ModifiedFileManager

abbrev LgtmM α := StateT State (Except String) α

/-- Delete all of the comments in the current review state.

This is used to prepare to fetch an updated state from the server. -/
private def resetCommentState : LgtmM Unit := do
  let s₀ ← get
  let manager₁ := s₀.fileManager.resetCommentState
  set { s₀ with commentManager := CommentManager.empty, fileManager := manager₁ }

end Lgtm
