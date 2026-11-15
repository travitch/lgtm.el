module

public import LgtmDeepLean.Lang.Eval
public import LgtmDeepLean.Lang.Syntax
meta import LgtmDeepLean.Lang.Syntax

/-! `lgtm` builds a plain `def`, which a `module` keeps to itself; the declarations of the model are
what the modules proving things about it read, so this module hands all of them out.  Exposed as well
as public: a proof about one of these declarations unfolds it to reach the `Expression` it carries,
and a type table built from them is read by `rfl`. -/
@[expose] public section

@[lgtm] structure CommentRef where
  id : string

@[lgtm] structure FileRef where
  path : string

@[lgtm] inductive FileVersion where
  | Base
  | Current

@[lgtm] inductive ThreadLocation where
  | TopLevel
  | LineNumber(int)

@[lgtm] def ThreadLocation.isTopLevel (l : inductive ThreadLocation) : bool :=
  match l with
  | TopLevel => true
  | LineNumber(_n) => false

@[lgtm] structure GitRevision where
  hash : string

@[lgtm] structure RepositoryRef where
  name : string
  path : string
  baseRevision: struct GitRevision

@[lgtm] inductive ModificationType where
  | Modified
  | Added
  | Deleted
  | Renamed
  | Copied
  | TypeChange

@[lgtm] structure ModifiedFileRef where
  repositoryRef : struct RepositoryRef
  modificationType : inductive ModificationType
  baseFileName : string
  baseFileHash : struct GitRevision
  currentFileName : string
  currentFileHash : struct GitRevision

@[lgtm] structure CommentFileLocation where
  version : inductive FileVersion
  fileRef : struct ModifiedFileRef
  startLine : int
  startColumn : int
  endLine : int
  endColumn : int

@[lgtm] inductive CommentLocation where
  | TopLevel
  | FileLocation(struct CommentFileLocation)

@[lgtm] structure ServerId where
  id : string

@[lgtm] structure Comment where
  ref : struct CommentRef
  backendId : option (struct ServerId)
  location : inductive CommentLocation
  author : string
  createdTimestamp : int
  updatedTimestamp : int
  parent : option (struct ServerId)
  replyToId : option (struct ServerId)
  content : string

@[lgtm] def Comment.isPersistedToServer (c : struct Comment) : bool :=
  match c.backendId with
  | none => false
  | some(_t) => true

@[lgtm] structure CommentThread where
  value : struct CommentRef
  children : list (struct CommentRef)

@[lgtm] structure CommentThreads where
  commentTreeNodes : hashmap (struct CommentRef) (struct CommentThread)
  serverCommentIds : hashmap (struct ServerId) (struct CommentRef)
  locationRoots : hashmap (inductive ThreadLocation) (list (struct CommentRef))

@[lgtm] def CommentThreads.empty : struct CommentThreads :=
   new CommentThreads { commentTreeNodes = hashmap(struct CommentRef, struct CommentThread),
                        serverCommentIds = hashmap(struct ServerId, struct CommentRef),
                        locationRoots = hashmap(inductive ThreadLocation, list (struct CommentRef))
                      }

@[lgtm] structure SelectedComment where
  version : inductive FileVersion
  thread : struct CommentThread
  comment : struct CommentRef

@[lgtm] structure CommentManager where
  comments : hashmap (struct CommentRef) (struct Comment)
  topLevelThreads : struct CommentThreads
  selectedComment : option (struct SelectedComment)

@[lgtm] structure Repository where
  name : string
  path : string
  baseRevision : struct GitRevision
  commits : list (tuple(struct GitRevision, string))

-- TODO: Need boolean conjunction
--
-- @[lgtm] def repositoryRefMatches (repository : struct Repository)
--   (ref : struct RepositoryRef) : bool

@[lgtm] structure ModifiedFileState where
  ref : struct ModifiedFileRef
  fileRef : struct FileRef
  selectedComment : option (struct SelectedComment)
  baseThreads : struct CommentThreads
  currentThreads : struct CommentThreads

@[lgtm] structure ModifiedFileManager where
  state : hashmap (struct ModifiedFileRef) (struct ModifiedFileState)
  modifiedFiles : list (struct ModifiedFileRef)

@[lgtm] structure ChangesetStatus where
  status : string

@[lgtm] structure Configuration where
  user : string
  changesetId : string
  repositories : list (struct Repository)
  author : string
  createdAt : int
  status : struct ChangesetStatus
  createComment : (struct Comment) -> option (struct ServerId)
  getRemoteConversations : (struct ModifiedFileManager) -> option (list (struct Comment))

@[lgtm] structure State where
  configuration : struct Configuration
  activeReviewedFile : option (struct ModifiedFileRef)
  commentBeingEdited : option (struct Comment)
  commentManager : struct CommentManager
  fileManager : struct ModifiedFileManager

/-! ## What this module contributes to the model

`lgtm` builds one Lean declaration per IR declaration and nothing that collects them, so the lists
below are what says which declarations this module hands to `modelProgram` — the `Program` the model
as a whole is read as, assembled in `LgtmDeepLean.Model.Program` and type checked by
`LgtmDeepLean.Model.Tests`.

A declaration added above goes in the list for its kind.  One left out is not a Lean error; it is a
declaration nothing type checks, which is what `Model.Tests` has a check against. -/

/-- The structure types this module declares, in the order they are declared above. -/
def Model.Basic.structDecls : List StructDecl :=
  [CommentRef, FileRef, GitRevision, RepositoryRef, ModifiedFileRef,
   CommentFileLocation, ServerId, Comment, CommentThread, CommentThreads,
   SelectedComment, CommentManager, Repository, ModifiedFileState,
   ModifiedFileManager, ChangesetStatus, Configuration, State]

/-- The inductive types this module declares, in the order they are declared above. -/
def Model.Basic.inductiveDecls : List InductiveDecl :=
  [FileVersion, ThreadLocation, ModificationType, CommentLocation]

/-- The functions this module declares, in the order they are declared above. -/
def Model.Basic.funcDecls : List FuncDecl :=
  [CommentThreads.empty, ThreadLocation.isTopLevel, Comment.isPersistedToServer]

end
