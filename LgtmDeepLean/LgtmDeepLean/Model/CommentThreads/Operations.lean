module

public import LgtmDeepLean.Model.Basic
meta import LgtmDeepLean.Lang.Syntax

public import LgtmDeepLean.Model.CommentManager.Operations
public import LgtmDeepLean.Model.Location.Operations

@[expose] public section


lgtm def CommentThreads.isEmpty (threads : struct CommentThreads) : bool :=
  length (toList threads.locationRoots) == 0

lgtm def CommentThreads.commentCount (threads : struct CommentThreads) : int :=
  length (toList threads.commentTreeNodes)

-- Sort the thread lists at each thread location
lgtm def CommentThreads.asAlist.sortThreadLists (threads : struct CommentThreads) (manager : struct CommentManager) (commentThreadRoots : tuple(inductive ThreadLocation, list (struct Comment))) : tuple(inductive ThreadLocation, list (struct CommentThread)) :=
  let sortedRoots = sortOn commentThreadRoots.1 (fun (c : struct Comment) => c.createdTimestamp) in
  let lookupThreadForComment = fun (c : struct Comment) => match threads.commentTreeNodes[c.ref] with
      | none => unreachable "Comments are required to have entries in CommentManager" : struct CommentThread
      | some(thread) => thread in
  let sortedThreads = map list sortedRoots lookupThreadForComment in
  tuple(commentThreadRoots.0, sortedThreads)

-- Probably need to map the thread roots into a list of comments first to keep things simpler in the lower levels
--
-- That will require a map over to `option comment` values with an unreachable case if it fails (which we'll prove away)
lgtm def CommentThreads.asAlist (threads : struct CommentThreads) (manager : struct CommentManager) : list (tuple(inductive ThreadLocation, list (struct CommentThread))) :=
  let refToComment = fun (commentRef : struct CommentRef) =>
      match CommentManager.get(manager, commentRef) with
      | none => unreachable "Comment references must be in the CommentManager" : struct Comment
      | some(c) => c in
  let lookupCommentForRef = fun (entry : tuple(inductive ThreadLocation, list (struct CommentRef))) =>
      let loc = entry.0 in
      let threadsAtLoc = entry.1 in
      let rootCommentsAtLoc = map list threadsAtLoc refToComment
      in tuple(loc, rootCommentsAtLoc) in
  let locatedRootComments = map list (toList threads.locationRoots) lookupCommentForRef in
  let sortThreadsAtLocation = fun (locatedThreads : tuple(inductive ThreadLocation, list (struct Comment))) =>
         (CommentThreads.asAlist.sortThreadLists(threads, manager, locatedThreads)) in
  let threadsSortedAtLocations = map list locatedRootComments sortThreadsAtLocation in
  sortBy threadsSortedAtLocations (fun (lt1 : tuple(inductive ThreadLocation, list (struct CommentThread))) (lt2 : tuple(inductive ThreadLocation, list (struct CommentThread))) => ThreadLocation.compare(lt1.0, lt2.0))

lgtm def CommentThreads.toThreadsOrdered (threads : struct CommentThreads) (manager : struct CommentManager) : list (struct CommentThread) :=
  flatMap CommentThreads.asAlist(threads, manager) (fun (locThreads : tuple(inductive ThreadLocation, list (struct CommentThread))) => locThreads.1)


lgtm def CommentThreads.rootComments (threads : struct CommentThreads) (manager : struct CommentManager) : list (struct Comment) :=
  map list CommentThreads.toThreadsOrdered(threads, manager) (fun (tree : struct CommentThread) => match CommentManager.get(manager, tree.value) with
    | none => unreachable "Comments must be defined in the CommentManager" : struct Comment
    | some(c) => c)

def Model.CommentThreads.funcDecls : List FuncDecl :=
  [CommentThreads.isEmpty, CommentThreads.commentCount, CommentThreads.asAlist.sortThreadLists, CommentThreads.asAlist, CommentThreads.toThreadsOrdered, CommentThreads.rootComments]

end
