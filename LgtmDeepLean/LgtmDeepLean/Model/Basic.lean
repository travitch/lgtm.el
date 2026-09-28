module

public import LgtmDeepLean.Lang.Syntax
meta import LgtmDeepLean.Lang.Syntax

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
