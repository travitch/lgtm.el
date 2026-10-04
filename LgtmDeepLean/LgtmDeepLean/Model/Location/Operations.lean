module

public import LgtmDeepLean.Model.Basic
meta import LgtmDeepLean.Lang.Syntax
meta import LgtmDeepLean.Model.Basic

@[expose] public section

lgtm def CommentLocation.isTopLevel (loc : inductive CommentLocation) : bool :=
  match loc with
  | TopLevel => true
  | FileLocation(_loc) => false

lgtm def CommentLocation.asThreadLocation (loc : inductive CommentLocation) : inductive ThreadLocation :=
  match loc with
  | TopLevel => new ThreadLocation.TopLevel()
  | FileLocation(floc) => new ThreadLocation.LineNumber(floc.startLine)

def Model.Location.funcDecls : List FuncDecl :=
  [CommentLocation.isTopLevel, CommentLocation.asThreadLocation]

end
