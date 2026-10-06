module

public import LgtmDeepLean.Model.Basic
public import LgtmDeepLean.Model.CommentThreads.Operations
meta import LgtmDeepLean.Lang.Syntax
meta import LgtmDeepLean.Model.Basic
meta import LgtmDeepLean.Model.CommentThreads.Operations

@[expose] public section

lgtm def CommentManager.empty : struct CommentManager :=
  new CommentManager { comments = hashmap(struct CommentRef, struct Comment),
                       topLevelThreads = CommentThreads.empty(),
                       selectedComment = none : struct SelectedComment
                     }

lgtm def CommentManager.get (manager : struct CommentManager) (ref : struct CommentRef) : option (struct Comment) :=
  manager.comments[ref]

def Model.CommentManager.funcDecls : List FuncDecl :=
  [CommentManager.empty, CommentManager.get]

end
