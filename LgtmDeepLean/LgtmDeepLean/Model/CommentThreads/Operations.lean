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

/-- Given a current SELECTION, select the next available thread (if any).

The VERSION is included because the user can switch files; as there is
only one global selection, if the user selects the next comment in a
different file, the whole selection resets.

The linear order is as established in the ordering defined by THREADS.
The MANAGER is required to get information about comments. -/
lgtm def CommentThreads.nextThread (threads : struct CommentThreads) (manager : struct CommentManager) (version : inductive FileVersion) (selection : struct SelectedComment) : option (struct SelectedComment) :=
  let orderedThreads = CommentThreads.toThreadsOrdered(threads, manager) in
  if version == selection.version then {
    match findIndex orderedThreads (fun (thread : struct CommentThread) => thread.value == selection.thread.value) with
      | none => none : struct SelectedComment
      | some(currentIndex) =>
        let nextIndex = min (currentIndex + 1) (length orderedThreads - 1) in
        let nextThread = match orderedThreads[nextIndex] with
            | none => unreachable "Thread indexing is required to be total" : struct CommentThread
            | some(thread) => thread in
        some (new SelectedComment { version = version, thread = nextThread, comment = nextThread.value })
  } else {
    match orderedThreads with
      | [] => none : struct SelectedComment
      | firstThread :: _rest => some (new SelectedComment { version = version, thread = firstThread, comment = firstThread.value })
  }

/-- Given a current SELECTION, select the previous available thread (if any).

The VERSION is included because the user can switch files; as there is
only one global selection, if the user selects the next comment in a
different file, the whole selection resets.

The linear order is as established in the ordering defined by THREADS.
The MANAGER is required to get information about comments. -/
lgtm def CommentThreads.previousThread (threads : struct CommentThreads) (manager : struct CommentManager) (version : inductive FileVersion) (selection : struct SelectedComment) : option (struct SelectedComment) :=
  let orderedThreads = CommentThreads.toThreadsOrdered(threads, manager) in
  if version == selection.version then {
    match findIndex orderedThreads (fun (thread : struct CommentThread) => thread.value == selection.thread.value) with
      | none => none : struct SelectedComment
      | some(currentIndex) =>
        let previousIndex = if currentIndex == 0 then { 0 } else { currentIndex - 1 } in
        let previousThread = match orderedThreads[previousIndex] with
            | none => unreachable "Thread indexing was proved to be total" : struct CommentThread
            | some(pt) => pt in
        some (new SelectedComment { version = version, thread = previousThread, comment = previousThread.value })
  } else {
    match orderedThreads with
      | [] => none : struct SelectedComment
      | firstThread :: rest => match reverse (firstThread :: rest) with
        | [] => unreachable "Already proved that the list is non-empty" : option (struct SelectedComment)
        | last :: _rest => some(new SelectedComment { version = version, thread = last, comment = last.value })
  }

def Model.CommentThreads.funcDecls : List FuncDecl :=
  [ CommentThreads.isEmpty
  , CommentThreads.commentCount
  , CommentThreads.asAlist.sortThreadLists
  , CommentThreads.asAlist
  , CommentThreads.toThreadsOrdered
  , CommentThreads.rootComments
  , CommentThreads.nextThread
  , CommentThreads.previousThread
  ]

end
