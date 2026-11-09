module

public import LgtmDeepLean.Model.Basic
meta import LgtmDeepLean.Lang.Syntax

public import LgtmDeepLean.Model.CommentManager.Operations

@[expose] public section


lgtm def CommentThreads.isEmpty (threads : struct CommentThreads) : bool :=
  length (toList threads.locationRoots) == 0

lgtm def CommentThreads.commentCount (threads : struct CommentThreads) : int :=
  length (toList threads.commentTreeNodes)

/- lgtm def compareThreadsByTimestamp (manager : struct CommentManager) (t1 : struct CommentThread) (t2 : struct CommentThread) : bool :=
 -   match CommentManager.get(manager, t1.value) with
 -   | none => unreachable "a thread's comment is in the manager" : bool
 -   | some(c1) =>
 -     match CommentManager.get(manager, t2.value) with
 -     | none => unreachable "a thread's comment is in the manager" : bool
 -     | some(c2) => c1.createdTimestamp < c2.createdTimestamp -/

-- Sort the thread lists at each thread location
lgtm def CommentThreads.asAlist.sortThreadLists (threads : struct CommentThreads) (manager : struct CommentManager) (commentThreadRoots : tuple(inductive ThreadLocation, list (struct Comment))) : tuple(inductive ThreadLocation, list (struct CommentThread)) :=
  let sortedRoots = sort commentThreadRoots.1 (fun (c : struct Comment) => c.createdTimestamp) in
  let sortedThreads = map list sortedRoots (fun (c : struct Comment) => match threads.commentTreeNodes[c.ref] with
      | none => unreachable "Comments are required to have entries in CommentManager" : struct CommentThread
      | some(thread) => thread) in
  tuple(commentThreadRoots.0, sortedThreads)

-- Probably need to map the thread roots into a list of comments first to keep things simpler in the lower levels
--
-- That will require a map over to `option comment` values with an unreachable case if it fails (which we'll prove away)
lgtm def CommentThreads.asAlist (threads : struct CommentThreads) (manager : struct CommentManager) : list (tuple(inductive ThreadLocation, list (struct CommentThread))) :=
  let locatedRootComments = map list (toList threads.locationRoots) (fun (entry : tuple(inductive ThreadLocation, list (struct CommentRef))) =>
      let loc = entry.0 in
      let threadsAtLoc = entry.1 in
      let rootCommentsAtLoc = map list threadsAtLoc (fun (commentRef : struct CommentRef) =>
        match CommentManager.get(manager, commentRef) with
        | none => unreachable "Comment references must be in the CommentManager" : struct Comment
        | some(c) => c)
      in tuple(loc, rootCommentsAtLoc)) in
  let threadsSortedAtLocations = map list locatedRootComments (fun (locatedThreads : tuple(inductive ThreadLocation, list (struct Comment))) =>
         (CommentThreads.asAlist.sortThreadLists(threads, manager, locatedThreads))) in
  [:tuple(inductive ThreadLocation, list (struct CommentThread))]

def Model.CommentThreads.funcDecls : List FuncDecl :=
  [CommentThreads.isEmpty, CommentThreads.commentCount, CommentThreads.asAlist.sortThreadLists, CommentThreads.asAlist]

end
