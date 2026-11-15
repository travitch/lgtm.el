module

public import LgtmDeepLean.Model.Basic
meta import LgtmDeepLean.Lang.Syntax

@[expose] public section

@[lgtm] def ThreadLocation.compare (loc1 : inductive ThreadLocation) (loc2 : inductive ThreadLocation) : bool :=
  match loc1 with
  | TopLevel => true
  | LineNumber(n1) => match loc2 with
    | TopLevel => false
    | LineNumber(n2) => n1 <= n2

@[lgtm] def CommentLocation.isTopLevel (loc : inductive CommentLocation) : bool :=
  match loc with
  | TopLevel => true
  | FileLocation(_loc) => false

@[lgtm] def CommentLocation.asThreadLocation (loc : inductive CommentLocation) : inductive ThreadLocation :=
  match loc with
  | TopLevel => new ThreadLocation.TopLevel()
  | FileLocation(floc) => new ThreadLocation.LineNumber(floc.startLine)

def Model.Location.funcDecls : List FuncDecl :=
  [CommentLocation.isTopLevel, CommentLocation.asThreadLocation, ThreadLocation.compare]

end
