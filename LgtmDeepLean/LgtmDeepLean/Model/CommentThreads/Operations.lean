module

public import LgtmDeepLean.Model.Basic
meta import LgtmDeepLean.Lang.Syntax

public import LgtmDeepLean.Model.CommentManager.Operations
public import LgtmDeepLean.Model.Location.Operations

@[expose] public section


@[lgtm] def CommentThreads.isEmpty (threads : struct CommentThreads) : bool :=
  length (toList threads.locationRoots) == 0

@[lgtm] def CommentThreads.commentCount (threads : struct CommentThreads) : int :=
  length (toList threads.commentTreeNodes)

-- Sort the thread lists at each thread location
@[lgtm] def CommentThreads.asAlist.sortThreadLists (threads : struct CommentThreads) (manager : struct CommentManager) (commentThreadRoots : tuple(inductive ThreadLocation, list (struct Comment))) : tuple(inductive ThreadLocation, list (struct CommentThread)) :=
  let sortedRoots := sortOn commentThreadRoots.1 (fun (c : struct Comment) => c.createdTimestamp);
  let lookupThreadForComment := fun (c : struct Comment) => match threads.commentTreeNodes[c.ref] with
      | none => (unreachable "Comments are required to have entries in CommentManager" : struct CommentThread)
      | some(thread) => thread;
  let sortedThreads := map sortedRoots lookupThreadForComment;
  tuple(commentThreadRoots.0, sortedThreads)

@[lgtm] def CommentThreads.asAlist (threads : struct CommentThreads) (manager : struct CommentManager) : list (tuple(inductive ThreadLocation, list (struct CommentThread))) :=
  let refToComment := fun (commentRef : struct CommentRef) =>
      match CommentManager.get(manager, commentRef) with
      | none => (unreachable "Comment references must be in the CommentManager" : struct Comment)
      | some(c) => c;
  let lookupCommentForRef := fun (entry : tuple(inductive ThreadLocation, list (struct CommentRef))) =>
      let loc := entry.0;
      let threadsAtLoc := entry.1;
      let rootCommentsAtLoc := map threadsAtLoc refToComment;
      tuple(loc, rootCommentsAtLoc);
  let locatedRootComments := map (toList threads.locationRoots) lookupCommentForRef;
  let sortThreadsAtLocation := fun (locatedThreads : tuple(inductive ThreadLocation, list (struct Comment))) =>
         (CommentThreads.asAlist.sortThreadLists(threads, manager, locatedThreads));
  let threadsSortedAtLocations := map locatedRootComments sortThreadsAtLocation;
  sortBy threadsSortedAtLocations (fun (lt1 : tuple(inductive ThreadLocation, list (struct CommentThread))) (lt2 : tuple(inductive ThreadLocation, list (struct CommentThread))) => ThreadLocation.compare(lt1.0, lt2.0))

@[lgtm] def CommentThreads.toThreadsOrdered (threads : struct CommentThreads) (manager : struct CommentManager) : list (struct CommentThread) :=
  flatMap CommentThreads.asAlist(threads, manager) (fun (locThreads : tuple(inductive ThreadLocation, list (struct CommentThread))) => locThreads.1)


@[lgtm] def CommentThreads.rootComments (threads : struct CommentThreads) (manager : struct CommentManager) : list (struct Comment) :=
  map CommentThreads.toThreadsOrdered(threads, manager) (fun (tree : struct CommentThread) => match CommentManager.get(manager, tree.value) with
    | none => (unreachable "Comments must be defined in the CommentManager" : struct Comment)
    | some(c) => c)

/-- Given a current SELECTION, select the next available thread (if any).

The VERSION is included because the user can switch files; as there is
only one global selection, if the user selects the next comment in a
different file, the whole selection resets.

The linear order is as established in the ordering defined by THREADS.
The MANAGER is required to get information about comments. -/
@[lgtm] def CommentThreads.nextThread (threads : struct CommentThreads) (manager : struct CommentManager) (version : inductive FileVersion) (selection : struct SelectedComment) : option (struct SelectedComment) :=
  let orderedThreads := CommentThreads.toThreadsOrdered(threads, manager);
  let expectThreadAt := fun (idx : int) => match orderedThreads[idx] with
    | none => (unreachable "Thread indexing is required to be total" : struct CommentThread)
    | some(thread) => thread;
  if version == selection.version then (
    match findIndex orderedThreads (fun (thread : struct CommentThread) => thread.value == selection.thread.value) with
      | none => (none : struct SelectedComment)
      | some(currentIndex) =>
        let nextIndex := min (currentIndex + 1) (length orderedThreads - 1);
        let nextThread := expectThreadAt(nextIndex);
        some (new SelectedComment { version = version, thread = nextThread, comment = nextThread.value })
  ) else (
    match orderedThreads with
      | [] => (none : struct SelectedComment)
      | firstThread :: _rest => some (new SelectedComment { version = version, thread = firstThread, comment = firstThread.value })
  )

/-- Given a current SELECTION, select the previous available thread (if any).

The VERSION is included because the user can switch files; as there is
only one global selection, if the user selects the next comment in a
different file, the whole selection resets.

The linear order is as established in the ordering defined by THREADS.
The MANAGER is required to get information about comments. -/
@[lgtm] def CommentThreads.previousThread (threads : struct CommentThreads) (manager : struct CommentManager) (version : inductive FileVersion) (selection : struct SelectedComment) : option (struct SelectedComment) :=
  let orderedThreads := CommentThreads.toThreadsOrdered(threads, manager);
  let expectThreadAt := fun (idx : int) => match orderedThreads[idx] with
    | none => (unreachable "Thread indexing is required to be total" : struct CommentThread)
    | some(thread) => thread;
  if version == selection.version then (
    match findIndex orderedThreads (fun (thread : struct CommentThread) => thread.value == selection.thread.value) with
      | none => (none : struct SelectedComment)
      | some(currentIndex) =>
        let previousIndex := if currentIndex == 0 then ( 0 ) else ( currentIndex - 1 );
        let previousThread := expectThreadAt(previousIndex);
        some (new SelectedComment { version = version, thread = previousThread, comment = previousThread.value })
  ) else (
    match orderedThreads with
      | [] => (none : struct SelectedComment)
      | firstThread :: rest => match reverse (firstThread :: rest) with
        | [] => (unreachable "Already proved that the list is non-empty" : option (struct SelectedComment))
        | last :: _rest => some(new SelectedComment { version = version, thread = last, comment = last.value })
  )

@[lgtm, forward] def CommentThread.linearizeRecWithFuel (threads : struct CommentThreads) (manager : struct CommentManager) (fuel : int) (thread : struct CommentThread) : list (struct Comment)

@[lgtm] def CommentThread.linearizeRecWithFuel (threads : struct CommentThreads) (manager : struct CommentManager) (fuel : int) (thread : struct CommentThread) : list (struct Comment) :=
  if fuel == 0 then (
    [: struct Comment]
  ) else (
    let expectComment := fun (ref : struct CommentRef) => match CommentManager.get(manager, ref) with
      | none => (unreachable "Comments are required to be present in the manager" : struct Comment)
      | some(c) => c;
    let comparisonFunction := fun (a : struct CommentRef) (b : struct CommentRef) => expectComment(a).createdTimestamp <= expectComment(b).createdTimestamp;
    let sortedChildren := sortBy thread.children comparisonFunction;
    expectComment(thread.value) :: flatMap sortedChildren (fun (childRef : struct CommentRef) => match threads.commentTreeNodes[childRef] with
      | none => (unreachable "All comments must have an entry in commentTreeNodes" : list (struct Comment))
      | some(childThread) => CommentThread.linearizeRecWithFuel(threads, manager, fuel - 1, childThread))
  )

@[lgtm] def CommentThread.linearize (thread : struct CommentThread) (threads : struct CommentThreads) (manager : struct CommentManager) : list (struct Comment) :=
  CommentThread.linearizeRecWithFuel(threads, manager, length (toList threads.commentTreeNodes), thread)

/-- Given a SELECTION, select the next comment in the linear order.

    This requires the comment MANAGER to sort comments and the THREADS
    structure to find the other comments in the thread. -/
@[lgtm] def CommentThreads.nextCommentInThread (threads : struct CommentThreads) (manager : struct CommentManager) (selection : struct SelectedComment) : struct SelectedComment :=
  let selectedThread := selection.thread;
  let linearizedComments := CommentThread.linearize(selectedThread, threads, manager);
  let linearizedCommentRefs := map linearizedComments (fun (c : struct Comment) => c.ref);
  let currentlySelectedRef := selection.comment;
  let matchesSelectedRef := fun (ref : struct CommentRef) => ref == currentlySelectedRef;
  let currentlySelectedIndex := match findIndex linearizedCommentRefs matchesSelectedRef with
    | none => (unreachable "The selected comment must exist in the linearized thread" : int)
    | some(idx) => idx;
  let nextIndex := min (currentlySelectedIndex + 1) (length linearizedCommentRefs - 1);
  let nextCommentRef := match linearizedCommentRefs[nextIndex] with
    | none => (unreachable "The next comment index must exist in the linearized comment list" : struct CommentRef)
    | some(r) => r;
  new SelectedComment { version = selection.version, thread = selection.thread, comment = nextCommentRef }

/-- Given a SELECTION, select the previous comment in the linear order.

    This requires the comment MANAGER to sort comments and the THREADS
    structure to find the other comments in the thread. -/
@[lgtm] def CommentThreads.previousCommentInThread (threads : struct CommentThreads) (manager : struct CommentManager) (selection : struct SelectedComment) : struct SelectedComment :=
  let selectedThread := selection.thread;
  let linearizedComments := CommentThread.linearize(selectedThread, threads, manager);
  let linearizedCommentRefs := map linearizedComments (fun (c : struct Comment) => c.ref);
  let currentlySelectedRef := selection.comment;
  let matchesSelectedRef := fun (ref : struct CommentRef) => ref == currentlySelectedRef;
  let currentlySelectedIndex := match findIndex linearizedCommentRefs matchesSelectedRef with
    | none => (unreachable "The selected comment must exist in the linearized thread" : int)
    | some(idx) => idx;
  let nextIndex := max 0 (currentlySelectedIndex + 1);
  let nextCommentRef := match linearizedCommentRefs[nextIndex] with
    | none => (unreachable "The next comment index must exist in the linearized comment list" : struct CommentRef)
    | some(r) => r;
  new SelectedComment { version = selection.version, thread = selection.thread, comment = nextCommentRef }

def Model.CommentThreads.funcDecls : List FuncDecl :=
  [ CommentThreads.isEmpty
  , CommentThreads.commentCount
  , CommentThreads.asAlist.sortThreadLists
  , CommentThreads.asAlist
  , CommentThreads.toThreadsOrdered
  , CommentThreads.rootComments
  , CommentThreads.nextThread
  , CommentThreads.previousThread
  , CommentThreads.nextCommentInThread
  , CommentThreads.previousCommentInThread
  , CommentThread.linearize
  , CommentThread.linearizeRecWithFuel
  ]

end
