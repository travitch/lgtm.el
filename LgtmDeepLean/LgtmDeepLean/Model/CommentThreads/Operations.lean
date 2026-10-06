module

public import LgtmDeepLean.Model.Basic
meta import LgtmDeepLean.Lang.Syntax
meta import LgtmDeepLean.Model.Basic

@[expose] public section

lgtm def CommentThreads.empty : struct CommentThreads :=
   new CommentThreads { commentTreeNodes = hashmap(struct CommentRef, struct CommentThread),
                        serverCommentIds = hashmap(struct ServerId, struct CommentRef),
                        locationRoots = hashmap(inductive ThreadLocation, list (struct CommentRef))
                      }

lgtm def CommentThreads.isEmpty (threads : struct CommentThreads) : bool :=
  length (toList (threads.locationRoots)) == 0

def Model.CommentThreads.funcDecls : List FuncDecl :=
  [CommentThreads.empty, CommentThreads.isEmpty]

end
