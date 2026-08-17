import Std
import Init.System

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
  deriving Hashable, BEq

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
  deriving Hashable, BEq

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

def Comment.isPersistedToServer (c : Comment) : Bool := c.backendId.isSome

-- FIXME: Should this be a tree of comments instead? There should be no harm (it is fine in the current implementation)
--
-- Downside: The current implementation acts more like IORefs everywhere.  Mutations to comments here would
-- not work or be visible.  Therefore, keeping all of the comments actually in the manager instead is probably
-- the better design
abbrev CommentThread := Tree CommentRef

/-- Locations of threads for rendering purposes.

These locations are less precise than the comment locations and are just
used for the renderer to group threads appropriately. -/
private inductive ThreadLocation where
| topLevel
| lineNumber : Nat → ThreadLocation
deriving Hashable, BEq, Ord

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
  hHasNodeForComment : ∀ loc, loc ∈ locationRoots.values.flatMap id → commentTreeNodes.contains loc

private def CommentThreads.empty : CommentThreads := ⟨ Std.HashMap.emptyWithCapacity, Std.HashMap.emptyWithCapacity, Std.HashMap.emptyWithCapacity, by sorry, by sorry ⟩

/-- Extract an alist of threads grouped by location.

The list is sorted by location.  Each list at a given location is sorted by comment timestamp.
The comment manager is required to get access to those timestamps. -/
private def CommentThreads.asAlist (threads : CommentThreads) (manager : CommentManager) : List (ThreadLocation × List CommentThread) :=
  threads.locationRoots.toList.map (λ (loc, threadRoots) => (loc, List.map (λ commentRef => threads.commentTreeNodes.get commentRef sorry) threadRoots))

def hasConsistentLocationsPredicate (locations : List ThreadLocation) : Prop :=
  (∀ loc, loc ∈ locations → loc.isTopLevel) ∨ (∀ loc, loc ∈ locations → !loc.isTopLevel)

theorem CommentThreads.asAlist.hasConsistentLocations (threads : CommentThreads) (manager : CommentManager) :
  hasConsistentLocationsPredicate (List.map fst (threads.asAlist manager)) := by sorry

private def listIsSortedPredicate (locations : List ThreadLocation) : Prop :=
  match locations with
  | [] => True
  | loc :: rest => rest.all (λ other => (compare loc other).isLE) ∧ listIsSortedPredicate rest

theorem CommentThreads.asAlist.isSortedByLocation (threads : CommentThreads) (manager : CommentManager) :
  listIsSortedPredicate (List.map fst (threads.asAlist manager)) := by sorry

-- TODO: Add a theorem that the result of CommentThreads.asAlist is sorted
--
-- The alist is sorted by location
--
-- Each sub-list is sorted by the timestamp of the root

private structure CommentManager where
  comments : Std.HashMap CommentRef Comment
  topLevelThreads : CommentThreads

private def CommentManager.empty : CommentManager := ⟨Std.HashMap.emptyWithCapacity, CommentThreads.empty⟩

/-- The comment selected in the file review UI. -/
structure SelectedComment where
  version : FileVersion
  thread : CommentThread
  comment : CommentRef

/-- A hash of a git revision -/
private structure GitRevision where
  hash : String
  deriving Hashable, BEq

private structure RepositoryRef where
  /-- The name of the repository -/
  name : String
  /-- The path of the repository on disk -/
  path : System.FilePath
  /-- The revision that the changeset will be applied to in the repository -/
  baseRevision : GitRevision
  deriving Hashable, BEq

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
deriving Hashable, BEq

private structure ModifiedFileRef where
  repositoryRef : RepositoryRef
  modificationType : ModificationType
  baseFileName : String
  baseFileHash : GitRevision
  currentFileName : String
  currentFileHash : GitRevision
  deriving Hashable, BEq

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
  { fileManager with state := updatedState, hConsistentState := by sorry }

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
