module

public import LgtmDeepLean.Lang.Syntax
meta import LgtmDeepLean.Lang.Syntax

lgtm struct CommentRef {
  id : string
}

lgtm struct FileRef {
  path : string
}


/- Inductive: FileVersion -/

/- Inductive: ThreadLocation -/

lgtm struct GitRevision {
  hash : string
}

lgtm struct RepositoryRef {
  name : string,
  path : string,
  baseRevision: struct GitRevision
}

/- Inductive: ModificationType -/
