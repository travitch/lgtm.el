module

public import LgtmDeepLean.Lang.Eval
public import LgtmDeepLean.Lang.Syntax
meta import LgtmDeepLean.Lang.Syntax

/-! `lgtm` builds a plain `def`, which a `module` keeps to itself; the declarations of the model are
what the modules proving things about it read, so this module hands all of them out.  Exposed as well
as public: a proof about one of these declarations unfolds it to reach the `Expression` it carries,
and a type table built from them is read by `rfl`. -/
@[expose] public section

lgtm struct CommentRef {
  id : string
}

lgtm struct FileRef {
  path : string
}

lgtm inductive FileVersion {
  Base, Current
}

lgtm inductive ThreadLocation {
  TopLevel,
  LineNumber(int)
}

lgtm def ThreadLocation.isTopLevel (l : inductive ThreadLocation) : bool :=
  match l with
  | TopLevel => true
  | LineNumber(_n) => false

lgtm struct GitRevision {
  hash : string
}

lgtm struct RepositoryRef {
  name : string,
  path : string,
  baseRevision: struct GitRevision
}

lgtm inductive ModificationType {
  Modified,
  Added,
  Deleted,
  Renamed,
  Copied,
  TypeChange
}

lgtm struct ModifiedFileRef {
  repositoryRef : struct RepositoryRef,
  modificationType : inductive ModificationType,
  baseFileName : string,
  baseFileHash : struct GitRevision,
  currentFileName : string,
  currentFileHash : struct GitRevision
}

/-- Return the path of VERSION of the MODIFIED-FILE. -/
lgtm def pathOfFileAtVersion (version : inductive FileVersion) (modifiedFile : struct ModifiedFileRef) : string :=
  match version with
  | Base => modifiedFile.baseFileName
  | Current => modifiedFile.currentFileName

lgtm struct CommentFileLocation {
  version : inductive FileVersion,
  fileRef : struct ModifiedFileRef,
  startLine : int,
  startColumn : int,
  endLine : int,
  endColumn : int
}

lgtm inductive CommentLocation {
  TopLevel,
  FileLocation(struct CommentFileLocation)
}

lgtm struct ServerId {
  id : string
}

/-! ## What this module contributes to the model

`lgtm` builds one Lean declaration per IR declaration and nothing that collects them, so the lists
below are what says which declarations this module hands to `modelProgram` — the `Program` the model
as a whole is read as, assembled in `LgtmDeepLean.Model.Program` and type checked by
`LgtmDeepLean.Model.Tests`.

A declaration added above goes in the list for its kind.  One left out is not a Lean error; it is a
declaration nothing type checks, which is what `Model.Tests` has a check against. -/

/-- The structure types this module declares, in the order they are declared above. -/
def Model.Basic.structDecls : List StructDecl :=
  [CommentRef, FileRef, GitRevision, RepositoryRef, ModifiedFileRef, CommentFileLocation, ServerId]

/-- The inductive types this module declares, in the order they are declared above. -/
def Model.Basic.inductiveDecls : List InductiveDecl :=
  [FileVersion, ThreadLocation, ModificationType, CommentLocation]

/-- The functions this module declares, in the order they are declared above. -/
def Model.Basic.funcDecls : List FuncDecl :=
  [ThreadLocation.isTopLevel, pathOfFileAtVersion]

end
