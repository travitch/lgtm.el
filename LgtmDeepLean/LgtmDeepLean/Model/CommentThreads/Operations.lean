module

public import LgtmDeepLean.Model.Basic
meta import LgtmDeepLean.Lang.Syntax
meta import LgtmDeepLean.Model.Basic

public import LgtmDeepLean.Model.CommentManager.Operations
meta import LgtmDeepLean.Model.CommentManager.Operations

@[expose] public section


lgtm def CommentThreads.isEmpty (threads : struct CommentThreads) : bool :=
  length (toList threads.locationRoots) == 0

lgtm def CommentThreads.commentCount (threads : struct CommentThreads) : int :=
  length (toList threads.commentTreeNodes)

lgtm def compareThreadsByTimestamp (manager : struct CommentManager) (t1 : struct CommentThread) (t2 : struct CommentThread) : bool :=
  match CommentManager.get(manager, t1.value) with
  | none => unreachable "a thread's comment is in the manager" : bool
  | some(c1) =>
    match CommentManager.get(manager, t2.value) with
    | none => unreachable "a thread's comment is in the manager" : bool
    | some(c2) => c1.createdTimestamp < c2.createdTimestamp


/- lgtm def CommentThreads.asAlist.sortThreadLists (threads : struct CommentThreads) (manager : struct CommentManager) (commentThreads : tuple(struct ThreadLocation, list (struct CommentRef))) : tuple(struct ThreadLocation, list (struct CommentThread)) :=
 -   () -/

lgtm def CommentThreads.asAlist (threads : struct CommentThreads) (manager : struct CommentManager) : list (tuple(struct ThreadLocation, list (struct CommentThread))) :=
  [:tuple(struct ThreadLocation, list (struct CommentThread))]

def Model.CommentThreads.funcDecls : List FuncDecl :=
  [CommentThreads.isEmpty, CommentThreads.commentCount, compareThreadsByTimestamp, CommentThreads.asAlist]

end
