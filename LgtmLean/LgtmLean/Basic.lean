module

import Std
import Init.System
import Init.Data.List.Sort

import LgtmLean.Tree

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
  deriving Hashable, DecidableEq

/-- Locations of threads for rendering purposes.

These locations are less precise than the comment locations and are just
used for the renderer to group threads appropriately. -/
inductive ThreadLocation where
| topLevel
| lineNumber : Nat → ThreadLocation
deriving Hashable, Ord, DecidableEq

def ThreadLocation.isTopLevel : ThreadLocation → Bool
| .topLevel => true
| .lineNumber _ => false

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
  deriving Hashable, Inhabited, BEq

def CommentLocation.isTopLevel : CommentLocation → Bool
| .topLevel => true
| .fileLocation _ => false

def CommentLocation.asThreadLocation : CommentLocation → ThreadLocation
| .topLevel => .topLevel
| .fileLocation loc => .lineNumber loc.startLine

structure ServerId where
  id : String
  deriving Inhabited, Hashable, DecidableEq

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

def Comment.isPersistedToServer (c : Comment) : Bool := c.backendId.isSome

abbrev CommentThread := Tree CommentRef

instance : Inhabited (Tree CommentRef) where
  default := ⟨default, []⟩

/-- `descendant` is reachable from `root` in `nodes` by following zero or more `Tree.children`
links. Used by `CommentThreads.hAllCommentTreeNodesAreLive` to say every stored node belongs to
some displayed thread instead of being an orphan. -/
inductive CommentThreads.NodeReachable (nodes : Std.HashMap CommentRef CommentThread) :
    CommentRef → CommentRef → Prop
  | refl (root : CommentRef) : CommentThreads.NodeReachable nodes root root
  | step {root parent child : CommentRef} (h : CommentThreads.NodeReachable nodes root parent)
      (hparent : nodes.contains parent) (hchild : child ∈ (nodes.get parent hparent).children) :
      CommentThreads.NodeReachable nodes root child

/-- The collected threads for a scope (file version or top-level). -/
structure CommentThreads where
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

def CommentThreads.empty : CommentThreads := ⟨Std.HashMap.emptyWithCapacity, Std.HashMap.emptyWithCapacity, Std.HashMap.emptyWithCapacity, by simp, by simp, by simp, by simp, by simp⟩

/-- Whether there are any threads to show.

Note: this is based on `locationRoots` (what's actually reachable/displayable), not
`commentTreeNodes` (which can contain tree nodes that no location references). -/
def CommentThreads.isEmpty (threads : CommentThreads) : Bool :=
  threads.locationRoots.toList.all (fun p => p.2.isEmpty)

structure CommentManager where
  comments : Std.HashMap CommentRef Comment
  topLevelThreads : CommentThreads

def CommentManager.empty : CommentManager := ⟨Std.HashMap.emptyWithCapacity, CommentThreads.empty⟩

def CommentManager.get (manager : CommentManager) (ref : CommentRef) : Comment :=
  manager.comments[ref]!


/-- The comment selected in the file review UI. -/
structure SelectedComment where
  version : FileVersion
  thread : CommentThread
  comment : CommentRef

/-- A hash of a git revision -/
structure GitRevision where
  hash : String
  deriving Hashable, DecidableEq

structure RepositoryRef where
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

structure ModifiedFileRef where
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
structure ModifiedFileState where
  ref : ModifiedFileRef
  fileRef : FileRef
  selectedComment : Option SelectedComment
  baseThreads : CommentThreads
  currentThreads : CommentThreads

structure ModifiedFileManager where
  state : Std.HashMap ModifiedFileRef ModifiedFileState
  /-- The files affected by the change in a server-defined order.  This is stored
  separately to preserve that order, which would be lost with only the hash map. -/
  modifiedFiles : List ModifiedFileRef

  /-- Invariant: Each modified file ref has an entry in `state`. -/
  hConsistentState : ∀ modifiedFile, modifiedFile ∈ modifiedFiles ↔ state.contains modifiedFile

def ModifiedFileManager.resetCommentState (fileManager : ModifiedFileManager) : ModifiedFileManager :=
  let updatedState := fileManager.state.map (fun modifiedFileRef fileState =>
    {fileState with selectedComment := none,
                    baseThreads := CommentThreads.empty,
                    currentThreads := CommentThreads.empty})
  have hConsistent : ∀ modifiedFile, modifiedFile ∈ fileManager.modifiedFiles ↔ updatedState.contains modifiedFile := by
    intro modifiedFile
    simp only [updatedState, Std.HashMap.contains_map]
    exact fileManager.hConsistentState modifiedFile
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

structure State where
  configuration : Configuration
  activeReviewedFile : Option ModifiedFileRef
  commentBeingEdited : Option CommentRef
  commentManager : CommentManager
  fileManager : ModifiedFileManager

abbrev LgtmM α := StateT State (Except String) α

/-- Delete all of the comments in the current review state.

This is used to prepare to fetch an updated state from the server. -/
def resetCommentState : LgtmM Unit := do
  let s₀ ← get
  let manager₁ := s₀.fileManager.resetCommentState
  set { s₀ with commentManager := CommentManager.empty, fileManager := manager₁ }


def addRemoteComments (comments : List Comment) : LgtmM Unit := do
  pure ()
