module

public import LgtmDeepLean.Model.Basic
meta import LgtmDeepLean.Lang.Syntax
meta import LgtmDeepLean.Model.Basic

/-! # Comment locations and thread locations

Where a comment sits, where a thread sits, and the conversion from the first to the second: the two
declarations of the model that read `CommentLocation`.

What the relational semantics says they return for a top-level location is in
`LgtmDeepLean.Model.Location.Properties`.  The declarations are what `modelProgram` collects and the
facts about them are not, so a caller wanting the model as IR — to collect it, to extract it — reads
this module and does not take the proofs with it.

The declarations are for callers elsewhere to read, so, as in `Model.Basic`, this module hands out
and exposes everything it declares. -/
@[expose] public section

lgtm def CommentLocation.isTopLevel (loc : inductive CommentLocation) : bool :=
  match loc with
  | TopLevel => true
  | FileLocation(_loc) => false

lgtm def CommentLocation.asThreadLocation (loc : inductive CommentLocation) : inductive ThreadLocation :=
  match loc with
  | TopLevel => new ThreadLocation.TopLevel()
  | FileLocation(floc) => new ThreadLocation.LineNumber(floc.startLine)

/-! ## What this module contributes to the model

As in `Model.Basic`: what this module hands to `modelProgram`.  The types the two functions mention
are declared there, so there is no list of types here — a module that declares none of a kind leaves
that list out rather than writing it empty, and `Model.Program` reads only the lists that exist. -/

/-- The functions this module declares, in the order they are declared above. -/
def Model.Location.funcDecls : List FuncDecl :=
  [CommentLocation.isTopLevel, CommentLocation.asThreadLocation]

end
