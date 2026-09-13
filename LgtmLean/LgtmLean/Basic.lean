module

public import Std
import Init.System
import Init.Data.List.Sort

public import LgtmLean.Tree

/-- A reference that can be mapped to (mutable) comment contents -/
public structure CommentRef where
  /-- A unique identifier

  These are only unique within a session.
  -/
  id : String
  deriving Inhabited, Hashable, DecidableEq

public structure FileRef where
  path : String
  deriving Hashable, BEq

public inductive FileVersion where
  | base
  | current
  deriving Hashable, DecidableEq

/-- Locations of threads for rendering purposes.

These locations are less precise than the comment locations and are just
used for the renderer to group threads appropriately. -/
public inductive ThreadLocation where
| topLevel
| lineNumber : Nat → ThreadLocation
deriving Hashable, Ord, DecidableEq

@[expose] public def ThreadLocation.isTopLevel (loc : ThreadLocation) : Bool :=
match loc with
| .topLevel => true
| .lineNumber _ => false


/-- A hash of a git revision -/
public structure GitRevision where
  hash : String
  deriving Hashable, DecidableEq

public structure RepositoryRef where
  /-- The name of the repository -/
  name : String
  /-- The path of the repository on disk -/
  path : System.FilePath
  /-- The revision that the changeset will be applied to in the repository -/
  baseRevision : GitRevision
  deriving Hashable, DecidableEq

public inductive ModificationType where
| modified
| added
| deleted
| renamed
| copied
| typechange
deriving Hashable, DecidableEq

public structure ModifiedFileRef where
  repositoryRef : RepositoryRef
  modificationType : ModificationType
  baseFileName : String
  baseFileHash : GitRevision
  currentFileName : String
  currentFileHash : GitRevision
  deriving Hashable, DecidableEq

public structure CommentFileLocation where
  version : FileVersion
  fileRef : ModifiedFileRef
  startLine : Nat
  startColumn : Nat
  endLine : Nat
  endColumn : Nat
  deriving Hashable, BEq

public inductive CommentLocation where
  | fileLocation : CommentFileLocation → CommentLocation
  | topLevel : CommentLocation
  deriving Hashable, Inhabited, BEq

public def CommentLocation.isTopLevel (loc : CommentLocation) : Bool :=
match loc with
| .topLevel => true
| .fileLocation _ => false

@[expose] public def CommentLocation.asThreadLocation (loc : CommentLocation) : ThreadLocation :=
match loc with
| .topLevel => .topLevel
| .fileLocation loc => .lineNumber loc.startLine

/-- Cross-module callers (e.g. `completeCommentWithContent`) can't unfold `asThreadLocation` /
`isTopLevel` via plain `rfl`, since ordinary `def`s aren't unfolded for defeq checking outside
their defining module; this exposes the fact as a citable lemma instead. -/
@[simp] public theorem CommentLocation.topLevel_asThreadLocation_isTopLevel :
    CommentLocation.topLevel.asThreadLocation.isTopLevel = true := rfl

/-- The `fileLocation` counterpart of `topLevel_asThreadLocation_isTopLevel`, for the same
cross-module unfolding reason. -/
@[simp] public theorem CommentLocation.fileLocation_asThreadLocation_isTopLevel (loc : CommentFileLocation) :
    (CommentLocation.fileLocation loc).asThreadLocation.isTopLevel = false := rfl

private theorem CommentLocation.topLevel_isTopLevel_aux :
    CommentLocation.topLevel.isTopLevel = true := rfl

/-- The direct (non-`asThreadLocation`) counterpart of `topLevel_asThreadLocation_isTopLevel`, for the
same cross-module unfolding reason. -/
@[simp] public theorem CommentLocation.topLevel_isTopLevel :
    CommentLocation.topLevel.isTopLevel = true := topLevel_isTopLevel_aux

private theorem CommentLocation.fileLocation_isTopLevel_aux (loc : CommentFileLocation) :
    (CommentLocation.fileLocation loc).isTopLevel = false := rfl

/-- The `fileLocation` counterpart of `topLevel_isTopLevel`, for the same cross-module unfolding
reason. -/
@[simp] public theorem CommentLocation.fileLocation_isTopLevel (loc : CommentFileLocation) :
    (CommentLocation.fileLocation loc).isTopLevel = false := fileLocation_isTopLevel_aux loc

public structure ServerId where
  id : String
  deriving Inhabited, Hashable, DecidableEq

/-- The actual contents of a comment.

This is separated out from references, as references often need to be hashed
or compared for equality, which is expensive if the reference actually includes
all of the comment data. -/
public structure Comment where
  /-- The unique id assigned to this comment.

  For new comments this is a gensym.  For comments fetched from the server, it
  is the server id. -/
  ref : CommentRef
  /-- The id of the comment on the server side.  This is only populated for
  comments fetched from the server and for comments that are sent to the server
  (even if they are unpublished) -/
  backendId : Option ServerId
  /-- The location of the comment. -/
  location : CommentLocation
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

public def Comment.isPersistedToServer (c : Comment) : Bool := c.backendId.isSome

public abbrev CommentThread := Tree CommentRef

instance : Inhabited (Tree CommentRef) where
  default := ⟨default, []⟩

/-- `descendant` is reachable from `root` in `nodes` by following zero or more `Tree.children`
links. Used by `CommentThreads.hAllCommentTreeNodesAreLive` to say every stored node belongs to
some displayed thread instead of being an orphan. -/
public inductive CommentThreads.NodeReachable (nodes : Std.HashMap CommentRef CommentThread) :
    CommentRef → CommentRef → Prop
  | refl (root : CommentRef) : CommentThreads.NodeReachable nodes root root
  | step {root parent child : CommentRef} (h : CommentThreads.NodeReachable nodes root parent)
      (hparent : nodes.contains parent) (hchild : child ∈ (nodes.get parent hparent).children) :
      CommentThreads.NodeReachable nodes root child

/-- The collected threads for a scope (file version or top-level). -/
public structure CommentThreads where
  /-- The tree node for each comment. -/
  commentTreeNodes : Std.HashMap CommentRef CommentThread

  serverCommentIds : Std.HashMap ServerId CommentRef

  /-- The comment tree roots at each location.

  Note that the root comments are not stored in any particular order.
  They are sorted at access time. -/
  locationRoots : Std.HashMap ThreadLocation (List CommentRef)

  /-- Invariant: Either there is one location that is top or there are no locations that are top -/
  hLocationsConsistent : (∀ loc, loc ∈ locationRoots.keys → loc.isTopLevel ∧ locationRoots.size = 1) ∨ (∀ loc, loc ∈ locationRoots.keys → ¬ loc.isTopLevel)

  /-- All referenced comments have an associated node -/
  hHasNodeForComment : ∀ loc threadRoots, (loc, threadRoots) ∈ locationRoots.toList →
    ∀ ref, ref ∈ threadRoots → commentTreeNodes.contains ref

  hAllCommentTreeNodesAreLive : ∀ commentRef, commentRef ∈ commentTreeNodes.keys →
    ∃ loc threadsList, (loc, threadsList) ∈ locationRoots.toList ∧
      ∃ root ∈ threadsList, CommentThreads.NodeReachable commentTreeNodes root commentRef

  /-- The tree stored for a comment is actually rooted at that comment: `commentTreeNodes` is
  keyed consistently with the trees it stores. -/
  hCommentTreeNodeRootMatchesKey : ∀ ref (h : commentTreeNodes.contains ref), (commentTreeNodes.get ref h).value = ref

  /-- A comment can be the root of at most one thread: no `CommentRef` occurs twice across all of
  the (possibly per-location) thread-root lists. -/
  hLocationRootsNodup : (locationRoots.toList.flatMap Prod.snd).Nodup

  /-- Every ref appearing in some registered node's children is itself a registered node: the graph
  has no dangling child references. This is what lets reachability (`CommentThreads.NodeReachable`)
  imply that `CommentThread.linearize`'s traversal actually visits the node, instead of silently
  dropping an unregistered child. -/
  hChildrenAreRegistered : ∀ ref (h : commentTreeNodes.contains ref) (child : CommentRef),
    child ∈ (commentTreeNodes.get ref h).children → commentTreeNodes.contains child

  /-- Every server-tracked comment id has a registered tree node. Applies to every `CommentThreads`
  pool (`CommentManager.topLevelThreads` as well as each file's `ModifiedFileState.baseThreads` /
  `.currentThreads`), which is what lets `addCommentToThread` discharge its `hParentThreadRegistered`
  obligation for any pool via this field directly, regardless of whether the pool is the top-level
  one or a specific file's. -/
  hServerCommentIdsRegistered : ∀ sid (h : serverCommentIds.contains sid),
    commentTreeNodes.contains (serverCommentIds.get sid h)

public def CommentThreads.empty : CommentThreads :=
  ⟨Std.HashMap.emptyWithCapacity, Std.HashMap.emptyWithCapacity, Std.HashMap.emptyWithCapacity,
    by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩

/-- Any comment registered as some thread's parent in `threads` already has a live tree node --
`addCommentToThread`'s `hParentThreadRegistered` obligation, restated without the unused
`comment.parent = some parentId` hypothesis. Applies to any pool (`CommentManager.topLevelThreads`
as well as any file's `ModifiedFileState.baseThreads` / `.currentThreads`). -/
public theorem CommentThreads.hParentThreadRegistered_mem (threads : CommentThreads) :
    ∀ parentId (h : parentId ∈ threads.serverCommentIds),
      threads.serverCommentIds.get parentId h ∈ threads.commentTreeNodes :=
  fun parentId h => Std.HashMap.mem_iff_contains.mpr
    (threads.hServerCommentIdsRegistered parentId (Std.HashMap.mem_iff_contains.mp h))

/-- Whether there are any threads to show.

Note: this is based on `locationRoots` (what's actually reachable/displayable), not
`commentTreeNodes` (which can contain tree nodes that no location references). -/
public def CommentThreads.isEmpty (threads : CommentThreads) : Bool :=
  threads.locationRoots.toList.all (fun p => p.2.isEmpty)

/-- The comment selected in the file review UI. -/
public structure SelectedComment where
  version : FileVersion
  thread : CommentThread
  comment : CommentRef

/-- A selection is well-formed with respect to a set of `threads` when `sel.thread` is exactly the
live tree node recorded for it in `threads`, and `sel.comment` is actually reachable from that
node. This is the invariant needed to guarantee that indexing into the thread's linearization (as
done by `CommentThreads.nextCommentInThread` / `CommentThreads.previousCommentInThread`) never
falls out of bounds: it forces the linearization to be nonempty and to actually contain
`sel.comment`. -/
public def SelectedComment.WellFormed (threads : CommentThreads) (sel : SelectedComment) : Prop :=
  ∃ h : threads.commentTreeNodes.contains sel.thread.value,
    threads.commentTreeNodes.get sel.thread.value h = sel.thread ∧
    CommentThreads.NodeReachable threads.commentTreeNodes sel.thread.value sel.comment

/-- A well-formed selection's thread is registered, so `threads.commentTreeNodes` is nonempty.
This is the fact that ultimately makes indexing into the thread's linearization total: the
linearization always emits at least the thread's own node before it can run out of fuel. -/
theorem SelectedComment.WellFormed.commentTreeNodes_size_ne_zero {threads : CommentThreads} {sel : SelectedComment}
    (hWF : SelectedComment.WellFormed threads sel) : threads.commentTreeNodes.size ≠ 0 := by
  obtain ⟨h, -, -⟩ := hWF
  rw [← Std.HashMap.length_keys, ne_eq, List.length_eq_zero_iff]
  exact List.ne_nil_of_mem (Std.HashMap.mem_keys.mpr (Std.HashMap.contains_iff_mem.mp h))

public structure CommentManager where
  comments : Std.HashMap CommentRef Comment
  topLevelThreads : CommentThreads
  /-- The comment currently selected while browsing the changeset's top-level (unattached)
  threads, independent of any specific file's own selection. -/
  selectedComment : Option SelectedComment

  hSelectedCommentWellFormed : ∀ sel, selectedComment = some sel →
    SelectedComment.WellFormed topLevelThreads sel

  /-- `comments` is keyed consistently with its own values: the comment stored at a ref really is
  the comment with that ref. This is what lets `CommentManager.get` (which looks a `Comment` up by
  `CommentRef` and reports its `.ref`) actually report back the ref it was looked up by. -/
  hCommentsKeyedByRef : ∀ ref (h : comments.contains ref), (comments.get ref h).ref = ref

  /-- Every location key registered in `topLevelThreads` is actually a top-level location.
  `topLevelThreads` is the pool for unattached/top-level comments only; per-file comment pools
  (`ModifiedFileState.baseThreads` / `.currentThreads`) are the only place `.lineNumber` locations
  belong. This is what lets `completeCommentWithContent` satisfy `addCommentToThread`'s
  `hLocationScope` obligation when finalizing a top-level comment. -/
  hTopLevelThreadsAllTopLevel : ∀ loc, loc ∈ topLevelThreads.locationRoots.keys → loc.isTopLevel = true

  /-- Every comment registered as a tree node in `topLevelThreads` has actually been published (has
  a server-assigned `backendId`). Combined with `CommentManager.CommentBeingEditedWellFormed`, this
  is what lets `completeCommentWithContent` know the comment it is about to publish can't already be
  registered in a thread, satisfying `addCommentToThread`'s `hRefFresh` obligation. -/
  hTopLevelThreadsPublished : ∀ ref (_h : topLevelThreads.commentTreeNodes.contains ref),
    ∃ h' : comments.contains ref, (comments.get ref h').backendId.isSome

public def CommentManager.empty : CommentManager :=
  ⟨Std.HashMap.emptyWithCapacity, CommentThreads.empty, none, by simp, by simp,
    by simp [CommentThreads.empty], by simp [CommentThreads.empty]⟩

/-- Looking up the key just inserted into a `Std.HashMap` returns the inserted value -- the
proof-carrying counterpart of `Std.HashMap.getElem_insert_self`. -/
public theorem Std.HashMap.get_insert_self {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Std.HashMap α β} {k : α} {v : β} (h : (m.insert k v).contains k) :
    (m.insert k v).get k h = v := by
  have hmem : k ∈ m.insert k v := h
  show (m.insert k v).get k hmem = v
  rw [Std.HashMap.get_eq_getElem, Std.HashMap.getElem_insert]
  simp

/-- Looking up a key other than the one just inserted into a `Std.HashMap` is unaffected by the
insert -- the proof-carrying counterpart of `Std.HashMap.getElem_insert`'s `else` branch. -/
public theorem Std.HashMap.get_insert_of_ne {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Std.HashMap α β} {k a : α} {v : β} (hne : ¬ (k == a)) (h : (m.insert k v).contains a)
    (hc : m.contains a) :
    (m.insert k v).get a h = m.get a hc := by
  have hmem : a ∈ m.insert k v := h
  have hmem' : a ∈ m := hc
  show (m.insert k v).get a hmem = m.get a hmem'
  rw [Std.HashMap.get_eq_getElem, Std.HashMap.get_eq_getElem, Std.HashMap.getElem_insert]
  simp [hne]

public def CommentManager.get (manager : CommentManager) (ref : CommentRef) : Comment :=
  manager.comments[ref]!

/-- `CommentManager.get` actually reports back the ref it was looked up by, as long as that ref is
covered (has an entry in `comments` at all) -- otherwise `[ref]!` would silently fall back to
`default`. -/
public theorem CommentManager.get_ref_eq (manager : CommentManager) {ref : CommentRef}
    (h : manager.comments.contains ref) : (manager.get ref).ref = ref := by
  have hmem : ref ∈ manager.comments := Std.HashMap.mem_iff_contains.mpr h
  show (manager.comments[ref]!).ref = ref
  rw [← Std.HashMap.getElem_eq_getElem! (h' := hmem), ← Std.HashMap.get_eq_getElem (h := hmem)]
  exact manager.hCommentsKeyedByRef ref h

/-- `CommentManager.get` agrees with a direct, proof-carrying lookup into `comments` whenever the
ref is covered. This is what lets callers transport facts about `manager.comments.get ref h` (as
supplied by, e.g., `CommentManager.CommentBeingEditedWellFormed`) onto `manager.get ref`. -/
public theorem CommentManager.get_eq_getComments (manager : CommentManager) {ref : CommentRef}
    (h : manager.comments.contains ref) : manager.get ref = manager.comments.get ref h := by
  have hmem : ref ∈ manager.comments := Std.HashMap.mem_iff_contains.mpr h
  show manager.comments[ref]! = manager.comments.get ref h
  rw [← Std.HashMap.getElem_eq_getElem! (h' := hmem)]
  exact Std.HashMap.get_eq_getElem.symm

/-- Specializes `CommentThreads.hParentThreadRegistered_mem` to `topLevelThreads`. -/
public theorem CommentManager.hParentThreadRegistered_mem (manager : CommentManager) :
    ∀ parentId (h : parentId ∈ manager.topLevelThreads.serverCommentIds),
      manager.topLevelThreads.serverCommentIds.get parentId h ∈ manager.topLevelThreads.commentTreeNodes :=
  manager.topLevelThreads.hParentThreadRegistered_mem

/-- A comment that isn't even registered in `comments` can't already be registered as a tree node in
`topLevelThreads`: every registered node is backed by an entry in `comments`
(`hTopLevelThreadsPublished`). -/
public theorem CommentManager.notMem_topLevelThreads_of_unpublished (manager : CommentManager) (ref : CommentRef)
    (hFresh : ¬ manager.comments.contains ref) :
    ref ∉ manager.topLevelThreads.commentTreeNodes := by
  intro hmemTree
  obtain ⟨hExists', _⟩ := manager.hTopLevelThreadsPublished ref (Std.HashMap.mem_iff_contains.mp hmemTree)
  exact hFresh hExists'

/-- If every published ref in the old `comments` map is still published in a new `comments₁` map
(e.g. because `comments₁` only grows), `hTopLevelThreadsPublished` transfers to `comments₁` too:
`topLevelThreads` itself is unaffected, so this is exactly what `completeCommentWithContent` needs
to re-establish `CommentManager.hTopLevelThreadsPublished` after publishing a comment into some
*other* pool (a file's, not the top-level one). -/
public theorem CommentManager.hTopLevelThreadsPublished_of_preserve (manager : CommentManager)
    {comments₁ : Std.HashMap CommentRef Comment}
    (hPreserve : ∀ ref (h : manager.comments.contains ref), (manager.comments.get ref h).backendId.isSome →
      ∃ h' : comments₁.contains ref, (comments₁.get ref h').backendId.isSome) :
    ∀ ref' (_h : manager.topLevelThreads.commentTreeNodes.contains ref'),
      ∃ h' : comments₁.contains ref', (comments₁.get ref' h').backendId.isSome := by
  intro ref' h
  obtain ⟨hcOld, hpubOld⟩ := manager.hTopLevelThreadsPublished ref' h
  exact hPreserve ref' hcOld hpubOld

/-- `topLevelThreads`'s location keys stay in scope for a comment whose location actually is
top-level: they're all top-level themselves (`hTopLevelThreadsAllTopLevel`), which is exactly what
a top-level comment's location reduces to. -/
public theorem CommentManager.locationScope_of_topLevel (manager : CommentManager) {location : CommentLocation}
    (hloc : location = CommentLocation.topLevel) :
    ∀ loc', loc' ∈ manager.topLevelThreads.locationRoots.keys → loc'.isTopLevel = location.asThreadLocation.isTopLevel := by
  rw [hloc, CommentLocation.topLevel_asThreadLocation_isTopLevel]
  exact manager.hTopLevelThreadsAllTopLevel

/-- Inserting a comment at the ref it claims as its own preserves `hCommentsKeyedByRef`: the
freshly-inserted entry reports back the key it was inserted at, and every other entry is
unaffected (delegating to the old invariant). -/
public theorem CommentManager.hCommentsKeyedByRef_insert (manager : CommentManager) (ref : CommentRef)
    (comment : Comment) (href : comment.ref = ref) :
    ∀ ref' (h : (manager.comments.insert ref comment).contains ref'),
      ((manager.comments.insert ref comment).get ref' h).ref = ref' := by
  intro ref' h
  by_cases heq : ref = ref'
  · subst heq
    rw [Std.HashMap.get_insert_self, href]
  · have hne : ¬ (ref == ref') := by simpa [beq_iff_eq] using heq
    have hc : manager.comments.contains ref' := by
      have h' := h
      rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at h'
      rcases h' with h1 | h1
      · exact absurd h1 heq
      · exact h1
    rw [Std.HashMap.get_insert_of_ne hne h hc]
    exact manager.hCommentsKeyedByRef ref' hc

/-- Inserting a fresh, previously-unregistered comment (`ref`, `hFresh`) into `comments` preserves
the published status of every other ref: an already-registered ref can't be `ref` itself (since
`ref` wasn't registered), so its entry is untouched by the insert. Used by
`completeCommentWithContent` to transport `hTopLevelThreadsPublished` / `hFileThreadsPublished`
facts across publishing the being-edited comment. -/
public theorem CommentManager.preservePublished_insert (manager : CommentManager) {ref : CommentRef}
    (hFresh : ¬ manager.comments.contains ref) (comment : Comment) :
    ∀ ref' (h : manager.comments.contains ref'), (manager.comments.get ref' h).backendId.isSome →
      ∃ h' : (manager.comments.insert ref comment).contains ref',
        ((manager.comments.insert ref comment).get ref' h').backendId.isSome := by
  intro ref' h hpub
  have hne : ref' ≠ ref := fun heq => hFresh (heq ▸ h)
  have hc : (manager.comments.insert ref comment).contains ref' := by
    rw [Std.HashMap.contains_insert, Bool.or_eq_true]
    exact Or.inr h
  refine ⟨hc, ?_⟩
  have hne' : ¬ (ref == ref') := by simpa [beq_iff_eq] using (Ne.symm hne)
  rw [Std.HashMap.get_insert_of_ne hne' hc h]
  exact hpub

public structure Repository where
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

/--
The mutable state for a file that can be reviewed.

Note: This used to track the last position in each file but that wasn't used.
-/
public structure ModifiedFileState where
  ref : ModifiedFileRef
  fileRef : FileRef
  selectedComment : Option SelectedComment
  baseThreads : CommentThreads
  currentThreads : CommentThreads

  /-- If a comment is selected, it is well-formed with respect to whichever of `baseThreads` /
  `currentThreads` its `version` selects. -/
  hSelectedCommentWellFormed : ∀ sel, selectedComment = some sel →
    SelectedComment.WellFormed (match sel.version with
      | .base => baseThreads
      | .current => currentThreads) sel

  /-- Every location key registered in `baseThreads` is actually a file-scoped (non-top-level)
  location. `baseThreads`/`currentThreads` are the pools for this file's own comments only;
  `CommentManager.topLevelThreads` is the only place `.topLevel` locations belong. This is what
  lets `completeCommentWithContent` satisfy `addCommentToThread`'s `hLocationScope` obligation when
  finalizing a file-scoped comment. -/
  hBaseThreadsFileScoped : ∀ loc, loc ∈ baseThreads.locationRoots.keys → loc.isTopLevel = false

  /-- The `currentThreads` counterpart of `hBaseThreadsFileScoped`. -/
  hCurrentThreadsFileScoped : ∀ loc, loc ∈ currentThreads.locationRoots.keys → loc.isTopLevel = false

/-- `baseThreads`'s location keys stay in scope for a comment whose location actually is
file-scoped (non-top-level): they're all non-top-level themselves (`hBaseThreadsFileScoped`), which
is exactly what a file-scoped comment's location reduces to. The `ModifiedFileState` counterpart of
`CommentManager.locationScope_of_topLevel`. -/
public theorem ModifiedFileState.locationScope_of_base (modifiedFileState : ModifiedFileState)
    {location : CommentLocation} (hloc : location.asThreadLocation.isTopLevel = false) :
    ∀ loc', loc' ∈ modifiedFileState.baseThreads.locationRoots.keys →
      loc'.isTopLevel = location.asThreadLocation.isTopLevel := by
  rw [hloc]
  exact modifiedFileState.hBaseThreadsFileScoped

/-- The `currentThreads` counterpart of `ModifiedFileState.locationScope_of_base`. -/
public theorem ModifiedFileState.locationScope_of_current (modifiedFileState : ModifiedFileState)
    {location : CommentLocation} (hloc : location.asThreadLocation.isTopLevel = false) :
    ∀ loc', loc' ∈ modifiedFileState.currentThreads.locationRoots.keys →
      loc'.isTopLevel = location.asThreadLocation.isTopLevel := by
  rw [hloc]
  exact modifiedFileState.hCurrentThreadsFileScoped

public structure ModifiedFileManager where
  state : Std.HashMap ModifiedFileRef ModifiedFileState
  /-- The files affected by the change in a server-defined order.  This is stored
  separately to preserve that order, which would be lost with only the hash map. -/
  modifiedFiles : List ModifiedFileRef

  /-- Invariant: Each modified file ref has an entry in `state`. -/
  hConsistentState : ∀ modifiedFile, modifiedFile ∈ modifiedFiles ↔ state.contains modifiedFile

  /-- Invariant: `state` is keyed consistently with its own values -- the file state stored at a
  ref really is the file state with that ref. This is the `ModifiedFileManager` counterpart of
  `CommentManager.hCommentsKeyedByRef`, and is what lets a direct lookup of `state` by key (rather
  than a scan of `state.toList` for a matching `.ref`) recover the looked-up value's own `.ref` for
  free -- used by `completeCommentWithContent` to satisfy `CommentBeingEditedWellFormed`'s
  file-scoped obligation without a separate runtime check. -/
  hStateKeyedByRef : ∀ ref (h : state.contains ref), (state.get ref h).ref = ref

/-- Recovers proof-carrying `contains`/`get` facts from a successful direct lookup by key -- used
by `completeCommentWithContent` to look up the `ModifiedFileState` for a comment's file location,
now that the lookup key (`loc.fileRef`) is known upfront and doesn't need to be found by scanning
`state.toList` for a matching `.ref`. -/
public theorem ModifiedFileManager.contains_get_of_getElem? (fileManager : ModifiedFileManager)
    {fileRef : ModifiedFileRef} {modifiedFileState : ModifiedFileState}
    (hfound : fileManager.state[fileRef]? = some modifiedFileState) :
    ∃ h : fileManager.state.contains fileRef, fileManager.state.get fileRef h = modifiedFileState := by
  have hContainsFileRef : fileManager.state.contains fileRef := by
    rw [Std.HashMap.contains_eq_isSome_getElem?, hfound]; rfl
  refine ⟨hContainsFileRef, ?_⟩
  obtain ⟨_, hval⟩ := Std.HashMap.getElem?_eq_some_iff.mp hfound
  exact hval

/-- Inserting at an already-`contains`ed key preserves `hConsistentState`: the key set of `state`
is unchanged (only the value at `fileRef` is replaced). Used by `completeCommentWithContent` to
reestablish `ModifiedFileManager.hConsistentState` after updating one file's threads; shared
verbatim by the `.base` and `.current` cases since neither depends on which of the file's thread
pools changed. -/
public theorem ModifiedFileManager.hConsistentState_insert (fileManager : ModifiedFileManager)
    {fileRef : ModifiedFileRef} (hOldContains : fileManager.state.contains fileRef)
    (newFileState : ModifiedFileState) :
    ∀ modifiedFile, modifiedFile ∈ fileManager.modifiedFiles ↔
      (fileManager.state.insert fileRef newFileState).contains modifiedFile := by
  intro modifiedFile
  rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq]
  constructor
  · intro hmf
    by_cases heq : fileRef = modifiedFile
    · exact Or.inl heq
    · exact Or.inr ((fileManager.hConsistentState modifiedFile).mp hmf)
  · rintro (heq | hc)
    · rw [← heq]; exact (fileManager.hConsistentState fileRef).mpr hOldContains
    · exact (fileManager.hConsistentState modifiedFile).mpr hc

/-- Inserting a file state at the ref it claims as its own preserves `hStateKeyedByRef`: the
freshly-inserted entry reports back the key it was inserted at, and every other entry is untouched
(delegating to the old invariant). The `ModifiedFileManager` counterpart of
`CommentManager.hCommentsKeyedByRef_insert`. -/
public theorem ModifiedFileManager.hStateKeyedByRef_insert (fileManager : ModifiedFileManager)
    (fileRef : ModifiedFileRef) (newFileState : ModifiedFileState) (href : newFileState.ref = fileRef) :
    ∀ ref' (h : (fileManager.state.insert fileRef newFileState).contains ref'),
      ((fileManager.state.insert fileRef newFileState).get ref' h).ref = ref' := by
  intro ref' h
  by_cases heq : fileRef = ref'
  · subst heq
    rw [Std.HashMap.get_insert_self, href]
  · have hne : ¬ (fileRef == ref') := by simpa [beq_iff_eq] using heq
    have hc : fileManager.state.contains ref' := by
      have h' := h
      rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at h'
      rcases h' with h1 | h1
      · exact absurd h1 heq
      · exact h1
    rw [Std.HashMap.get_insert_of_ne hne h hc]
    exact fileManager.hStateKeyedByRef ref' hc

/-- The per-file update `ModifiedFileManager.resetCommentState` applies to every tracked file: clear
the selected comment and both thread pools. Factored out to its own declaration (rather than an
inline lambda) so it fully elaborates -- proof obligations included -- before `resetCommentState`
reasons about it; an inline lambda's `by simp` fields would still be pending synthetic metavariables
at that point, which breaks the `.ref`-preservation proof below. -/
private def ModifiedFileManager.resetFileState (fileState : ModifiedFileState) : ModifiedFileState :=
  {fileState with selectedComment := none,
                  baseThreads := CommentThreads.empty,
                  currentThreads := CommentThreads.empty,
                  hSelectedCommentWellFormed := by simp,
                  hBaseThreadsFileScoped := by simp [CommentThreads.empty],
                  hCurrentThreadsFileScoped := by simp [CommentThreads.empty]}

/-- `resetFileState` only touches `selectedComment`/`baseThreads`/`currentThreads`, so it leaves
`.ref` untouched. -/
private theorem ModifiedFileManager.resetFileState_ref (fileState : ModifiedFileState) :
    (ModifiedFileManager.resetFileState fileState).ref = fileState.ref := rfl

public def ModifiedFileManager.resetCommentState (fileManager : ModifiedFileManager) : ModifiedFileManager :=
  let updatedState : Std.HashMap ModifiedFileRef ModifiedFileState :=
    fileManager.state.map (fun _ fileState => ModifiedFileManager.resetFileState fileState)
  have hConsistent : ∀ modifiedFile, modifiedFile ∈ fileManager.modifiedFiles ↔ updatedState.contains modifiedFile := by
    intro modifiedFile
    simp only [updatedState, Std.HashMap.contains_map]
    exact fileManager.hConsistentState modifiedFile
  have hStateKeyedByRef : ∀ ref (h : updatedState.contains ref), (Std.HashMap.get updatedState ref h).ref = ref := by
    intro ref h
    have hOld : fileManager.state.contains ref := by simpa [updatedState, Std.HashMap.contains_map] using h
    have hfound : fileManager.state[ref]? = some (Std.HashMap.get fileManager.state ref hOld) :=
      Std.HashMap.getElem?_eq_some_iff.mpr ⟨hOld, Std.HashMap.get_eq_getElem.symm⟩
    have hupdated? : updatedState[ref]? =
        some (ModifiedFileManager.resetFileState (Std.HashMap.get fileManager.state ref hOld)) := by
      simp only [updatedState, Std.HashMap.getElem?_map, hfound, Option.map_some]
    obtain ⟨_, hEq⟩ := Std.HashMap.getElem?_eq_some_iff.mp hupdated?
    have hget : Std.HashMap.get updatedState ref h =
        ModifiedFileManager.resetFileState (Std.HashMap.get fileManager.state ref hOld) := hEq
    rw [hget, ModifiedFileManager.resetFileState_ref]
    exact fileManager.hStateKeyedByRef ref hOld
  { fileManager with state := updatedState, hConsistentState := hConsistent, hStateKeyedByRef := hStateKeyedByRef }

/-- After resetting comment state, every file's `baseThreads`/`currentThreads` are empty
(`CommentThreads.empty`), so any "every registered ref is published" obligation holds of them
vacuously -- used by `resetCommentState` to reestablish `State.hFileThreadsPublished` after
clearing all threads. -/
public theorem ModifiedFileManager.hFileThreadsPublished_resetCommentState (fileManager : ModifiedFileManager)
    (comments : Std.HashMap CommentRef Comment) :
    ∀ modifiedFileRef (h : fileManager.resetCommentState.state.contains modifiedFileRef),
      let modifiedFileState := fileManager.resetCommentState.state.get modifiedFileRef h
      (∀ ref (_hc : modifiedFileState.baseThreads.commentTreeNodes.contains ref),
        ∃ h' : comments.contains ref, (comments.get ref h').backendId.isSome) ∧
      (∀ ref (_hc : modifiedFileState.currentThreads.commentTreeNodes.contains ref),
        ∃ h' : comments.contains ref, (comments.get ref h').backendId.isSome) := by
  intro modifiedFileRef h
  have hget : fileManager.resetCommentState.state.get modifiedFileRef h =
      ModifiedFileManager.resetFileState
        (fileManager.state.get modifiedFileRef (by simpa [ModifiedFileManager.resetCommentState] using h)) := by
    simp only [ModifiedFileManager.resetCommentState]
    rw [Std.HashMap.get_eq_getElem, Std.HashMap.get_eq_getElem, Std.HashMap.getElem_map]
  simp only [hget, ModifiedFileManager.resetFileState]
  simp [CommentThreads.empty]

/-- The comment currently being edited is fresh (not yet registered in `comments` -- it's only
inserted there once it's published), hasn't been published yet, and (if it's a reply) its parent has
already been published into a live thread in the pool matching its own location: the top-level pool
for a top-level comment, or the matching file+version pool for a file-scoped one. This is exactly
what `completeCommentWithContent` needs in order to know that finalizing the edited comment can't
collide with an existing thread node, and that any parent it references is already safe to attach
to. -/
@[expose] public def CommentManager.CommentBeingEditedWellFormed (manager : CommentManager)
    (fileManager : ModifiedFileManager) (comment : Comment) : Prop :=
    ¬ manager.comments.contains comment.ref ∧
    comment.backendId = none ∧
    ∀ parentId, comment.parent = some parentId →
      match comment.location with
      | .topLevel => parentId ∈ manager.topLevelThreads.serverCommentIds
      | .fileLocation loc =>
        ∀ modifiedFileRef (modifiedFileState : ModifiedFileState),
          (modifiedFileRef, modifiedFileState) ∈ fileManager.state.toList →
          modifiedFileState.ref == loc.fileRef →
          parentId ∈ (match loc.version with
            | .base => modifiedFileState.baseThreads
            | .current => modifiedFileState.currentThreads).serverCommentIds

/-- If `comment` is the comment currently being edited, it's fresh (unregistered in `comments`),
unpublished, and (if it's a reply) its parent is already registered in the pool matching its
location. -/
public theorem CommentManager.get_of_commentBeingEditedWellFormed (manager : CommentManager)
    (fileManager : ModifiedFileManager) (comment : Comment)
    (hWF : manager.CommentBeingEditedWellFormed fileManager comment) :
    ¬ manager.comments.contains comment.ref ∧
    comment.backendId = none ∧
      ∀ parentId, comment.parent = some parentId →
        match comment.location with
        | .topLevel => parentId ∈ manager.topLevelThreads.serverCommentIds
        | .fileLocation loc =>
          ∀ modifiedFileRef (modifiedFileState : ModifiedFileState),
            (modifiedFileRef, modifiedFileState) ∈ fileManager.state.toList →
            modifiedFileState.ref == loc.fileRef →
            parentId ∈ (match loc.version with
              | .base => modifiedFileState.baseThreads
              | .current => modifiedFileState.currentThreads).serverCommentIds := hWF

/-- This would ideally be an inductive, but different servers can provide different statuses.  We just
take what they give us. -/
public structure ChangesetStatus where
  status : String

public structure Configuration where
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

  /-- A function to create a new comment (in unpublished state) on the server.

  Note that the `createComment` function technically performs IO to communicate with the server.  It
  isn't in IO because we don't really want `LgtmM` to need to be IO and complicate the proofs.  We
  can't really guarantee what that function will or won't do and it could technically violate any
  invariant.  Implementors should not do that.  If the `createComment` function fails, it should just
  return `none` and issue any warnings it wants in elisp.
  -/
  createComment : Comment → Option ServerId

  getRemoteConversations : ModifiedFileManager → Option (List Comment)

public structure State where
  configuration : Configuration
  activeReviewedFile : Option ModifiedFileRef
  commentBeingEdited : Option Comment
  commentManager : CommentManager
  fileManager : ModifiedFileManager

  /-- Whichever comment is currently being edited is well-formed: it exists, is unpublished, and any
  parent it references is already registered in the pool matching its own location. -/
  hCommentBeingEditedWellFormed : ∀ comment, commentBeingEdited = some comment →
    commentManager.CommentBeingEditedWellFormed fileManager comment

  /-- Every comment registered as a tree node in any file's `baseThreads` / `currentThreads` has
  actually been published (has a server-assigned `backendId`). The file-pool analogue of
  `CommentManager.hTopLevelThreadsPublished`. Combined with `hCommentBeingEditedWellFormed`, this is
  what lets `completeCommentWithContent` know a file-scoped comment it is about to publish can't
  already be registered in that file's thread pool, satisfying `addCommentToThread`'s `hRefFresh`
  obligation. -/
  hFileThreadsPublished : ∀ modifiedFileRef (h : fileManager.state.contains modifiedFileRef),
    (∀ ref (_hc : (fileManager.state.get modifiedFileRef h).baseThreads.commentTreeNodes.contains ref),
      ∃ h' : commentManager.comments.contains ref, (commentManager.comments.get ref h').backendId.isSome) ∧
    (∀ ref (_hc : (fileManager.state.get modifiedFileRef h).currentThreads.commentTreeNodes.contains ref),
      ∃ h' : commentManager.comments.contains ref, (commentManager.comments.get ref h').backendId.isSome)

/-- The `State.hFileThreadsPublished` counterpart of `CommentManager.hTopLevelThreadsPublished_of_preserve`:
if every published ref in the old `comments` map is still published in a new `comments₁` map, the
"every file's registered threads are published" invariant transfers to `comments₁` too, since no
file's `baseThreads`/`currentThreads` are touched. This is what `completeCommentWithContent` needs
to re-establish `State.hFileThreadsPublished` after publishing the being-edited comment (into
whichever pool actually changed). -/
public theorem State.hFileThreadsPublished_of_preserve (s : State)
    {comments₁ : Std.HashMap CommentRef Comment}
    (hPreserve : ∀ ref (h : s.commentManager.comments.contains ref),
      (s.commentManager.comments.get ref h).backendId.isSome →
      ∃ h' : comments₁.contains ref, (comments₁.get ref h').backendId.isSome) :
    ∀ modifiedFileRef (h : s.fileManager.state.contains modifiedFileRef),
      (∀ ref (_hc : (s.fileManager.state.get modifiedFileRef h).baseThreads.commentTreeNodes.contains ref),
        ∃ h' : comments₁.contains ref, (comments₁.get ref h').backendId.isSome) ∧
      (∀ ref (_hc : (s.fileManager.state.get modifiedFileRef h).currentThreads.commentTreeNodes.contains ref),
        ∃ h' : comments₁.contains ref, (comments₁.get ref h').backendId.isSome) := by
  intro modifiedFileRef h
  obtain ⟨hBase, hCurrent⟩ := s.hFileThreadsPublished modifiedFileRef h
  refine ⟨fun ref hc => ?_, fun ref hc => ?_⟩
  · obtain ⟨h', hpub'⟩ := hBase ref hc
    exact hPreserve ref h' hpub'
  · obtain ⟨h', hpub'⟩ := hCurrent ref hc
    exact hPreserve ref h' hpub'

/-- A comment that isn't even registered in `comments` can't already be registered as a tree node in
a file's `baseThreads`: every registered node there is backed by an entry in `comments`
(`hFileThreadsPublished`). The file-pool analogue of
`CommentManager.notMem_topLevelThreads_of_unpublished`. -/
public theorem State.notMem_baseThreads_of_unpublished (s : State) {ref : CommentRef}
    (hFresh : ¬ s.commentManager.comments.contains ref)
    {fileRef : ModifiedFileRef} (h : s.fileManager.state.contains fileRef) :
    ref ∉ (s.fileManager.state.get fileRef h).baseThreads.commentTreeNodes := by
  intro hmemPool
  obtain ⟨hExists', _⟩ := (s.hFileThreadsPublished fileRef h).1 ref (Std.HashMap.mem_iff_contains.mp hmemPool)
  exact hFresh hExists'

/-- The `currentThreads` counterpart of `State.notMem_baseThreads_of_unpublished`. -/
public theorem State.notMem_currentThreads_of_unpublished (s : State) {ref : CommentRef}
    (hFresh : ¬ s.commentManager.comments.contains ref)
    {fileRef : ModifiedFileRef} (h : s.fileManager.state.contains fileRef) :
    ref ∉ (s.fileManager.state.get fileRef h).currentThreads.commentTreeNodes := by
  intro hmemPool
  obtain ⟨hExists', _⟩ := (s.hFileThreadsPublished fileRef h).2 ref (Std.HashMap.mem_iff_contains.mp hmemPool)
  exact hFresh hExists'

/-- Publishing a file-scoped comment into `baseThreads` (via `addCommentToThread`, whose effect on
`commentTreeNodes` is summarized by `hNewBaseThreadsContains`) and storing the updated file state
back into `fileManager.state` preserves `State.hFileThreadsPublished`: every tree node in the
touched file's pools is still backed by a published comment (`comment₂` itself is newly published,
`hbackendId2`; everything else delegates to the old invariant via
`CommentManager.preservePublished_insert`), and every other file's pools are untouched. The
`.base`-version counterpart of `CommentManager.hTopLevelThreadsPublished_insert`. -/
public theorem State.hFileThreadsPublished_insert_base (s : State)
    {fileRef : ModifiedFileRef} {modifiedFileState : ModifiedFileState}
    (hOldContains : s.fileManager.state.contains fileRef)
    (hgetval : s.fileManager.state.get fileRef hOldContains = modifiedFileState)
    {editedCommentRef : CommentRef} (hFresh : ¬ s.commentManager.comments.contains editedCommentRef)
    {comment₂ : Comment} (href2 : comment₂.ref = editedCommentRef) {serverId : ServerId}
    (hbackendId2 : comment₂.backendId = some serverId)
    {newBaseThreads : CommentThreads}
    (hNewBaseThreadsContains : ∀ ref, newBaseThreads.commentTreeNodes.contains ref ↔
      modifiedFileState.baseThreads.commentTreeNodes.contains ref ∨ ref = comment₂.ref)
    {newFileState : ModifiedFileState} (hNewFileStateBase : newFileState.baseThreads = newBaseThreads)
    (hNewFileStateCurrent : newFileState.currentThreads = modifiedFileState.currentThreads)
    {newState : Std.HashMap ModifiedFileRef ModifiedFileState}
    (hNewState : newState = s.fileManager.state.insert fileRef newFileState)
    {newComments : Std.HashMap CommentRef Comment}
    (hNewComments : newComments = s.commentManager.comments.insert editedCommentRef comment₂) :
    ∀ modifiedFileRef' (h : newState.contains modifiedFileRef'),
      (∀ ref (_hc : (newState.get modifiedFileRef' h).baseThreads.commentTreeNodes.contains ref),
        ∃ h' : newComments.contains ref, (newComments.get ref h').backendId.isSome) ∧
      (∀ ref (_hc : (newState.get modifiedFileRef' h).currentThreads.commentTreeNodes.contains ref),
        ∃ h' : newComments.contains ref, (newComments.get ref h').backendId.isSome) := by
  subst hNewState hNewComments hgetval
  have hPreserve := s.commentManager.preservePublished_insert hFresh comment₂
  intro modifiedFileRef' h
  by_cases heq : fileRef = modifiedFileRef'
  · subst heq
    rw [Std.HashMap.get_insert_self, hNewFileStateBase, hNewFileStateCurrent]
    refine ⟨fun ref hc => ?_, fun ref hc => ?_⟩
    · rcases (hNewBaseThreadsContains ref).mp hc with hold | hnew
      · obtain ⟨hcOld, hpubOld⟩ := (s.hFileThreadsPublished fileRef hOldContains).1 ref hold
        exact hPreserve ref hcOld hpubOld
      · have hcNew : (s.commentManager.comments.insert editedCommentRef comment₂).contains editedCommentRef :=
          Std.HashMap.contains_insert_self
        rw [hnew, href2]
        refine ⟨hcNew, ?_⟩
        rw [Std.HashMap.get_insert_self, hbackendId2]
        rfl
    · obtain ⟨hcOld, hpubOld⟩ := (s.hFileThreadsPublished fileRef hOldContains).2 ref hc
      exact hPreserve ref hcOld hpubOld
  · have hne'' : ¬ (fileRef == modifiedFileRef') := by simpa [beq_iff_eq] using heq
    have hcOld : s.fileManager.state.contains modifiedFileRef' := by
      have h' := h
      rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at h'
      rcases h' with h1 | h1
      · exact absurd h1 heq
      · exact h1
    rw [Std.HashMap.get_insert_of_ne hne'' h hcOld]
    obtain ⟨hBase, hCurrent⟩ := s.hFileThreadsPublished modifiedFileRef' hcOld
    refine ⟨fun ref hc => ?_, fun ref hc => ?_⟩
    · obtain ⟨hc', hpub'⟩ := hBase ref hc
      exact hPreserve ref hc' hpub'
    · obtain ⟨hc', hpub'⟩ := hCurrent ref hc
      exact hPreserve ref hc' hpub'

/-- The `.current`-version counterpart of `State.hFileThreadsPublished_insert_base`. -/
public theorem State.hFileThreadsPublished_insert_current (s : State)
    {fileRef : ModifiedFileRef} {modifiedFileState : ModifiedFileState}
    (hOldContains : s.fileManager.state.contains fileRef)
    (hgetval : s.fileManager.state.get fileRef hOldContains = modifiedFileState)
    {editedCommentRef : CommentRef} (hFresh : ¬ s.commentManager.comments.contains editedCommentRef)
    {comment₂ : Comment} (href2 : comment₂.ref = editedCommentRef) {serverId : ServerId}
    (hbackendId2 : comment₂.backendId = some serverId)
    {newCurrentThreads : CommentThreads}
    (hNewCurrentThreadsContains : ∀ ref, newCurrentThreads.commentTreeNodes.contains ref ↔
      modifiedFileState.currentThreads.commentTreeNodes.contains ref ∨ ref = comment₂.ref)
    {newFileState : ModifiedFileState}
    (hNewFileStateBase : newFileState.baseThreads = modifiedFileState.baseThreads)
    (hNewFileStateCurrent : newFileState.currentThreads = newCurrentThreads)
    {newState : Std.HashMap ModifiedFileRef ModifiedFileState}
    (hNewState : newState = s.fileManager.state.insert fileRef newFileState)
    {newComments : Std.HashMap CommentRef Comment}
    (hNewComments : newComments = s.commentManager.comments.insert editedCommentRef comment₂) :
    ∀ modifiedFileRef' (h : newState.contains modifiedFileRef'),
      (∀ ref (_hc : (newState.get modifiedFileRef' h).baseThreads.commentTreeNodes.contains ref),
        ∃ h' : newComments.contains ref, (newComments.get ref h').backendId.isSome) ∧
      (∀ ref (_hc : (newState.get modifiedFileRef' h).currentThreads.commentTreeNodes.contains ref),
        ∃ h' : newComments.contains ref, (newComments.get ref h').backendId.isSome) := by
  subst hNewState hNewComments hgetval
  have hPreserve := s.commentManager.preservePublished_insert hFresh comment₂
  intro modifiedFileRef' h
  by_cases heq : fileRef = modifiedFileRef'
  · subst heq
    rw [Std.HashMap.get_insert_self, hNewFileStateBase, hNewFileStateCurrent]
    refine ⟨fun ref hc => ?_, fun ref hc => ?_⟩
    · obtain ⟨hcOld, hpubOld⟩ := (s.hFileThreadsPublished fileRef hOldContains).1 ref hc
      exact hPreserve ref hcOld hpubOld
    · rcases (hNewCurrentThreadsContains ref).mp hc with hold | hnew
      · obtain ⟨hcOld, hpubOld⟩ := (s.hFileThreadsPublished fileRef hOldContains).2 ref hold
        exact hPreserve ref hcOld hpubOld
      · have hcNew : (s.commentManager.comments.insert editedCommentRef comment₂).contains editedCommentRef :=
          Std.HashMap.contains_insert_self
        rw [hnew, href2]
        refine ⟨hcNew, ?_⟩
        rw [Std.HashMap.get_insert_self, hbackendId2]
        rfl
  · have hne'' : ¬ (fileRef == modifiedFileRef') := by simpa [beq_iff_eq] using heq
    have hcOld : s.fileManager.state.contains modifiedFileRef' := by
      have h' := h
      rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq] at h'
      rcases h' with h1 | h1
      · exact absurd h1 heq
      · exact h1
    rw [Std.HashMap.get_insert_of_ne hne'' h hcOld]
    obtain ⟨hBase, hCurrent⟩ := s.hFileThreadsPublished modifiedFileRef' hcOld
    refine ⟨fun ref hc => ?_, fun ref hc => ?_⟩
    · obtain ⟨hc', hpub'⟩ := hBase ref hc
      exact hPreserve ref hc' hpub'
    · obtain ⟨hc', hpub'⟩ := hCurrent ref hc
      exact hPreserve ref hc' hpub'

public def addToListAt [BEq α] [Hashable α] (key : α) (value : β) (m : Std.HashMap α (List β)) : Std.HashMap α (List β) :=
  match m[key]? with
  | none => m.insert key [value]
  | some lst => m.insert key (value :: lst)

public theorem addToListAt_eq_insert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (key : α) (value : β) (m : Std.HashMap α (List β)) :
    addToListAt key value m = m.insert key (value :: m.getD key []) := by
  unfold addToListAt
  rw [Std.HashMap.getD_eq_getD_getElem?]
  cases m[key]? with
  | none => rfl
  | some lst => rfl
