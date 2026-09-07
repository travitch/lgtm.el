module

public import LgtmLean.Basic
import all LgtmLean.Basic

public def compareLocatedCommentThreads (t₁ : ThreadLocation × List CommentThread) (t₂ : ThreadLocation × List CommentThread) : Bool :=
  match (t₁, t₂) with
  | ((.topLevel, _), _) => true
  | (_, (.topLevel, _)) => false
  | ((.lineNumber n₁, _), (.lineNumber n₂, _)) => n₁ ≤ n₂

public def compareThreadsByTimestamp (manager : CommentManager) (t₁ : CommentThread) (t₂ : CommentThread) : Bool :=
  (manager.get t₁.value).createdTimestamp ≤ (manager.get t₂.value).createdTimestamp

public def CommentThreads.asAlist.sortThreadLists (threads : CommentThreads) (manager : CommentManager)
  (subtype₁ : {x : ThreadLocation × List CommentRef // x ∈ threads.locationRoots.toList}) :
    ThreadLocation × List CommentThread :=
  let hPair := subtype₁.property
  let loc := subtype₁.val.1
  let threadRoots := subtype₁.val.2
  let commentThreads := threadRoots.attach.map (λ subtype₂ =>
    let href := subtype₂.property
    let commentRef := subtype₂.val
    let hMember := Std.HashMap.mem_iff_contains.mpr (threads.hHasNodeForComment loc threadRoots hPair commentRef href)
    threads.commentTreeNodes.get commentRef hMember)
  let sortedThreads := List.mergeSort commentThreads (compareThreadsByTimestamp manager)
  (loc, sortedThreads)

/-- Extract an alist of threads grouped by location.

The list is sorted by location.  Each list at a given location is sorted by comment timestamp.
The comment manager is required to get access to those timestamps. -/
public def CommentThreads.asAlist (threads : CommentThreads) (manager : CommentManager) : List (ThreadLocation × List CommentThread) :=
  let threadsAtLocationsWithMemberProofs := threads.locationRoots.toList.attach
  let unsorted := threadsAtLocationsWithMemberProofs.map (CommentThreads.asAlist.sortThreadLists threads manager)
  unsorted.mergeSort compareLocatedCommentThreads

/-- Return the threads in sorted order. -/
public def CommentThreads.toThreadsOrdered (threads : CommentThreads) (manager : CommentManager) : List CommentThread :=
  List.flatMap (λ p => Prod.snd p) (threads.asAlist manager)

/--
Given a collection of threads and a selection, return the next thread to select linearly.

The VERSION is included because the user can switch files; as there is only one global selection,
if the user selects the next comment in a different file, the whole selection resets.

The linear order is as established in the ordering defined by CommentThreads.

Note: It would be nice to keep the association between the selection and the threads objects it references.  Future work.
-/
public def CommentThreads.nextThread (threads : CommentThreads) (manager : CommentManager) (version : FileVersion) (selection : SelectedComment) : Option SelectedComment :=
  let orderedThreads := threads.toThreadsOrdered manager
  match version == selection.version, orderedThreads with
  | false, [] => none
  | false, firstThread :: _ => some ⟨version, firstThread, firstThread.value⟩
  | true, _ =>
    match orderedThreads.findIdx? (·.value == selection.thread.value) with
    | none => none
    | some curIdx =>
      /- This should be provable because if we found the thread in the list, the list cannot be empty -/
      let nextIdx := Nat.min (curIdx + 1) (orderedThreads.length - 1)
      let nextThread := orderedThreads[nextIdx]!
      some ⟨version, nextThread, nextThread.value⟩

public def CommentThreads.previousThread (threads : CommentThreads) (manager : CommentManager) (version : FileVersion) (selection : SelectedComment) : Option SelectedComment :=
  let orderedThreads := threads.toThreadsOrdered manager
  match version == selection.version, orderedThreads with
  | false, [] => none
  | false, a :: as =>
    let lastThread := (a :: as).getLast (List.cons_ne_nil a as)
    some ⟨version, lastThread, lastThread.value⟩
  | true, _ =>
    match orderedThreads.findIdx? (·.value == selection.thread.value) with
    | none => none
    | some curIdx =>
      let prevIdx := if curIdx == 0 then 0 else curIdx - 1
      let prevThread := orderedThreads[prevIdx]!
      some ⟨version, prevThread, prevThread.value⟩

/-- Depth-first walk of `thread`'s descendants, resolving child refs against `threads` up to
`fuel` levels deep. `fuel := threads.commentTreeNodes.size` in `CommentThread.linearize` is enough
to reach every node of a genuine (cycle-free) thread, since such a thread's depth cannot exceed
its node count. Children are sorted by timestamp at each level, matching `CommentThreads.asAlist`. -/
public def CommentThread.linearizeRecWithFuel (threads : CommentThreads) (manager : CommentManager) (fuel : Nat) (thread : CommentThread) : List Comment :=
match fuel with
| 0 => []
| fuel + 1 =>
    let comparisonFunction := fun a b => (compare (manager.get a).createdTimestamp (manager.get b).createdTimestamp).isLE
    let sortedChildren := thread.children.mergeSort comparisonFunction
    manager.get thread.value :: sortedChildren.flatMap (fun childRef =>
      match threads.commentTreeNodes[childRef]? with
      | none => []
      | some childThread => CommentThread.linearizeRecWithFuel threads manager fuel childThread)

/-- Linearize a comment THREAD (belonging to `threads`) with a depth-first traversal. -/
public def CommentThread.linearize (thread : CommentThread) (threads : CommentThreads) (manager : CommentManager) : List Comment :=
  CommentThread.linearizeRecWithFuel threads manager threads.commentTreeNodes.size thread

private theorem CommentThread.linearizeRecWithFuel.ne_nil_of_fuel_ne_zero (threads : CommentThreads)
    (manager : CommentManager) {fuel : Nat} (hFuel : fuel ≠ 0) (thread : CommentThread) :
    CommentThread.linearizeRecWithFuel threads manager fuel thread ≠ [] := by
  cases fuel with
  | zero => exact absurd rfl hFuel
  | succ n => simp [CommentThread.linearizeRecWithFuel]

/-- More fuel only ever adds to the traversal, never removes from it: increasing `fuel` by one keeps
every previously-emitted comment. -/
private theorem CommentThread.linearizeRecWithFuel.subset_succ (threads : CommentThreads) (manager : CommentManager)
    (fuel : Nat) (thread : CommentThread) :
    CommentThread.linearizeRecWithFuel threads manager fuel thread ⊆
      CommentThread.linearizeRecWithFuel threads manager (fuel + 1) thread := by
  induction fuel generalizing thread with
  | zero => exact List.nil_subset _
  | succ n ih =>
    intro x hx
    unfold CommentThread.linearizeRecWithFuel at hx ⊢
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_self
    · refine List.mem_cons_of_mem _ ?_
      rw [List.mem_flatMap] at hx ⊢
      obtain ⟨childRef, hcr, hxc⟩ := hx
      refine ⟨childRef, hcr, ?_⟩
      cases hlookup : threads.commentTreeNodes[childRef]? with
      | none => rw [hlookup] at hxc; exact absurd hxc (by simp)
      | some childThread => rw [hlookup] at hxc; exact ih childThread hxc

/-- More fuel never removes anything, for any amount of extra fuel (not just one more). -/
private theorem CommentThread.linearizeRecWithFuel.subset_of_le (threads : CommentThreads) (manager : CommentManager)
    {fuel fuel' : Nat} (hle : fuel ≤ fuel') (thread : CommentThread) :
    CommentThread.linearizeRecWithFuel threads manager fuel thread ⊆
      CommentThread.linearizeRecWithFuel threads manager fuel' thread := by
  induction fuel' with
  | zero =>
    have hfz : fuel = 0 := by omega
    subst hfz
    exact fun _ h => h
  | succ n ih =>
    by_cases heq : fuel = n + 1
    · exact heq ▸ fun _ h => h
    · exact fun x hx =>
        CommentThread.linearizeRecWithFuel.subset_succ threads manager n thread (ih (by omega) hx)

/-- If `childRef` is one of `parentThread`'s children, everything reachable from `childRef`'s own
node is also reachable from `parentThread`, one level of fuel later: `linearizeRecWithFuel`
recurses into every child via `flatMap`, so `childRef`'s own recursive call is literally one of the
pieces being unioned together. -/
private theorem CommentThread.linearizeRecWithFuel.subset_of_mem_children (threads : CommentThreads)
    (manager : CommentManager) (parentThread : CommentThread) (childRef : CommentRef)
    (hChildMem : childRef ∈ parentThread.children) (hChildContains : threads.commentTreeNodes.contains childRef)
    (fuel : Nat) :
    CommentThread.linearizeRecWithFuel threads manager fuel (threads.commentTreeNodes.get childRef hChildContains) ⊆
      CommentThread.linearizeRecWithFuel threads manager (fuel + 1) parentThread := by
  intro x hx
  show x ∈ CommentThread.linearizeRecWithFuel threads manager (fuel + 1) parentThread
  unfold CommentThread.linearizeRecWithFuel
  refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨childRef, ?_, ?_⟩)
  · exact List.mem_mergeSort.mpr hChildMem
  · rw [Std.HashMap.getElem?_eq_some_getElem hChildContains]
    exact hx

/-- A concrete walk from `root` to `endpoint` through `nodes`, following `.children` links,
recorded as the list of nodes visited (built by appending one node at a time). Unlike
`CommentThreads.NodeReachable`, a `PathTo` carries its own witness list, which lets us bound its
length and connect it to `CommentThread.linearizeRecWithFuel`'s fuel. -/
private inductive CommentThreads.PathTo (nodes : Std.HashMap CommentRef CommentThread) (root : CommentRef) :
    CommentRef → List CommentRef → Prop
  | refl : CommentThreads.PathTo nodes root root [root]
  | step {parent child : CommentRef} {path : List CommentRef} (h : CommentThreads.PathTo nodes root parent path)
      (hparent : nodes.contains parent) (hchild : child ∈ (nodes.get parent hparent).children) :
      CommentThreads.PathTo nodes root child (path ++ [child])

/-- If `x` occurs anywhere along a walk, there is a (no-longer-than) walk to `x` too: either the
walk to the immediately preceding node (a `step`'s hypothesis) already reaches `x`, or `x` is the
last node just reached by the outer walk itself. Either way, the walk found is a `Nodup` sublist of
the original (in fact, a prefix), so it stays `Nodup` given the original is. -/
private theorem CommentThreads.PathTo.exists_nodup_of_mem {nodes : Std.HashMap CommentRef CommentThread}
    {root endpoint : CommentRef} {path : List CommentRef} (h : CommentThreads.PathTo nodes root endpoint path)
    (hNodup : path.Nodup) (x : CommentRef) (hx : x ∈ path) :
    ∃ path', CommentThreads.PathTo nodes root x path' ∧ path'.Nodup := by
  induction h with
  | refl =>
    obtain rfl := List.mem_singleton.mp hx
    exact ⟨[x], .refl, by simp⟩
  | step h hparent hchild ih =>
    rw [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ih (List.nodup_append.mp hNodup).1 hx
    · exact ⟨_, .step h hparent hchild, hNodup⟩

/-- `CommentThreads.NodeReachable`'s existential, possibly-repeating witness can always be turned
into a genuine (`Nodup`) walk: extend the walk one node at a time, and whenever the new node has
already been visited, jump back to that earlier occurrence instead of revisiting it. -/
private theorem CommentThreads.NodeReachable.exists_nodup_pathTo {nodes : Std.HashMap CommentRef CommentThread}
    {root target : CommentRef} (h : CommentThreads.NodeReachable nodes root target) :
    ∃ path, CommentThreads.PathTo nodes root target path ∧ path.Nodup := by
  induction h with
  | refl => exact ⟨[root], .refl, by simp⟩
  | step h hparent hchild ih =>
    obtain ⟨path, hpath, hnodup⟩ := ih
    rename_i parent child
    by_cases hmem : child ∈ path
    · exact hpath.exists_nodup_of_mem hnodup child hmem
    · refine ⟨path ++ [child], hpath.step hparent hchild,
        List.nodup_append.mpr ⟨hnodup, by simp, ?_⟩⟩
      intro a ha b hb heq
      subst heq
      rw [List.mem_singleton] at hb
      subst hb
      exact hmem ha

/-- Every node along a walk is registered, provided its own root is and every registered node's
children are (`CommentThreads.hChildrenAreRegistered`). -/
private theorem CommentThreads.PathTo.mem_registered {nodes : Std.HashMap CommentRef CommentThread}
    (hChildrenRegistered : ∀ ref (h : nodes.contains ref) (child : CommentRef),
      child ∈ (nodes.get ref h).children → nodes.contains child)
    {root endpoint : CommentRef} {path : List CommentRef} (h : CommentThreads.PathTo nodes root endpoint path)
    (hRootContains : nodes.contains root) :
    ∀ x ∈ path, nodes.contains x := by
  induction h with
  | refl => simpa using hRootContains
  | step h hparent hchild ih =>
    intro x hx
    rw [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ih x hx
    · exact hChildrenRegistered _ hparent x hchild

/-- A `Nodup` walk can never be longer than the number of registered nodes: its elements are a
`Nodup` subset of `nodes.keys`. -/
private theorem CommentThreads.PathTo.length_le_size {nodes : Std.HashMap CommentRef CommentThread}
    (hChildrenRegistered : ∀ ref (h : nodes.contains ref) (child : CommentRef),
      child ∈ (nodes.get ref h).children → nodes.contains child)
    {root endpoint : CommentRef} {path : List CommentRef} (h : CommentThreads.PathTo nodes root endpoint path)
    (hNodup : path.Nodup) (hRootContains : nodes.contains root) :
    path.length ≤ nodes.size := by
  rw [← Std.HashMap.length_keys]
  refine List.Nodup.length_le_of_subset hNodup (fun x hx => ?_)
  exact Std.HashMap.mem_keys.mpr (Std.HashMap.contains_iff_mem.mp (h.mem_registered hChildrenRegistered hRootContains x hx))

/-- The whole point of tracking a walk explicitly: `endpoint`'s own recursive call, at any fuel
`k+1`, is contained in `root`'s recursive call at `path.length + k` fuel. Proved by induction on the
walk, chaining `CommentThread.linearizeRecWithFuel.subset_of_mem_children` (one more link in the
walk costs one more level of fuel) with the induction hypothesis (the rest of the walk already fits
in `path.length - 1` extra fuel). -/
private theorem CommentThreads.PathTo.linearize_subset {threads : CommentThreads} (manager : CommentManager)
    (hChildrenRegistered : ∀ ref (h : threads.commentTreeNodes.contains ref) (child : CommentRef),
      child ∈ (threads.commentTreeNodes.get ref h).children → threads.commentTreeNodes.contains child)
    {root endpoint : CommentRef} {path : List CommentRef}
    (h : CommentThreads.PathTo threads.commentTreeNodes root endpoint path)
    (h₀ : threads.commentTreeNodes.contains root) :
    ∃ he : threads.commentTreeNodes.contains endpoint, ∀ k : Nat,
      CommentThread.linearizeRecWithFuel threads manager (k + 1) (threads.commentTreeNodes.get endpoint he) ⊆
        CommentThread.linearizeRecWithFuel threads manager (path.length + k) (threads.commentTreeNodes.get root h₀) := by
  induction h with
  | refl => exact ⟨h₀, fun k x hx => by simpa [Nat.add_comm] using hx⟩
  | step h hparent hchild ih =>
    obtain ⟨heParent, ihsub⟩ := ih
    rename_i parent child path'
    have heChild := hChildrenRegistered parent hparent child hchild
    refine ⟨heChild, fun k => ?_⟩
    have hstep := CommentThread.linearizeRecWithFuel.subset_of_mem_children threads manager
      (threads.commentTreeNodes.get parent hparent) child hchild heChild (k + 1)
    have hchain := ihsub (k + 1)
    simp only [List.length_append, List.length_singleton]
    intro x hx
    exact (by omega : path'.length + (k + 1) = path'.length + 1 + k) ▸ hchain (hstep hx)

/-- The linearization of any thread is nonempty as soon as `threads.commentTreeNodes` is: the
recursion always emits the thread's own node before its fuel (`threads.commentTreeNodes.size`) can
run out. -/
private theorem CommentThread.linearize.ne_nil_of_commentTreeNodes_size_ne_zero (thread : CommentThread)
    (threads : CommentThreads) (manager : CommentManager) (hSize : threads.commentTreeNodes.size ≠ 0) :
    thread.linearize threads manager ≠ [] :=
  CommentThread.linearizeRecWithFuel.ne_nil_of_fuel_ne_zero threads manager hSize thread

/-- At fuel 1, a node's own recursive call emits nothing but itself (no fuel remains to descend
into any child), and reports back its own ref (given coverage, so `manager.get` doesn't fall back
to `default`). -/
private theorem CommentThread.mem_linearizeRecWithFuel_one (threads : CommentThreads) (manager : CommentManager)
    (hCoverage : ∀ ref, threads.commentTreeNodes.contains ref → manager.comments.contains ref)
    (ref : CommentRef) (h : threads.commentTreeNodes.contains ref) :
    ref ∈ (CommentThread.linearizeRecWithFuel threads manager 1 (threads.commentTreeNodes.get ref h)).map (·.ref) := by
  have hval : (threads.commentTreeNodes.get ref h).value = ref := threads.hCommentTreeNodeRootMatchesKey ref h
  have hgetref : (manager.get (threads.commentTreeNodes.get ref h).value).ref = ref := by
    rw [hval]; exact manager.get_ref_eq (hCoverage ref h)
  simp [CommentThread.linearizeRecWithFuel, hgetref]

/-- A well-formed selection's linearized comment-ref list is always nonempty, which is exactly what
totality of the indexing in `nextCommentInThread` / `previousCommentInThread` needs. -/
private theorem SelectedComment.WellFormed.linearizedCommentRefs_ne_nil {threads : CommentThreads}
    {sel : SelectedComment} (manager : CommentManager) (hWF : SelectedComment.WellFormed threads sel) :
    ((sel.thread.linearize threads manager).map (·.ref)) ≠ [] := by
  rw [ne_eq, List.map_eq_nil_iff]
  exact CommentThread.linearize.ne_nil_of_commentTreeNodes_size_ne_zero sel.thread threads manager
    hWF.commentTreeNodes_size_ne_zero

/-- The comment a well-formed selection names is genuinely present in its thread's linearization --
not just that the linearization is nonempty, but that this specific comment is the one found. This
needs `hCoverage`: every registered thread node must have actual comment content available in
`manager`, which is not implied by `SelectedComment.WellFormed` alone (it says nothing about
`manager`), so it is required separately here. -/
theorem SelectedComment.WellFormed.comment_mem_linearizedCommentRefs {threads : CommentThreads}
    {sel : SelectedComment} (manager : CommentManager)
    (hCoverage : ∀ ref, threads.commentTreeNodes.contains ref → manager.comments.contains ref)
    (hWF : SelectedComment.WellFormed threads sel) :
    sel.comment ∈ (sel.thread.linearize threads manager).map (·.ref) := by
  obtain ⟨h, heq, hreach⟩ := hWF
  obtain ⟨path, hpath, hnodup⟩ := hreach.exists_nodup_pathTo
  obtain ⟨he, hsub⟩ := hpath.linearize_subset manager threads.hChildrenAreRegistered h
  have hlen : path.length ≤ threads.commentTreeNodes.size :=
    hpath.length_le_size threads.hChildrenAreRegistered hnodup h
  obtain ⟨c, hc, hcref⟩ := List.mem_map.mp (CommentThread.mem_linearizeRecWithFuel_one threads manager hCoverage
    sel.comment he)
  have hc' : c ∈ CommentThread.linearizeRecWithFuel threads manager (path.length + 0)
      (threads.commentTreeNodes.get sel.thread.value h) := hsub 0 hc
  have hc'' : c ∈ CommentThread.linearizeRecWithFuel threads manager threads.commentTreeNodes.size
      (threads.commentTreeNodes.get sel.thread.value h) :=
    CommentThread.linearizeRecWithFuel.subset_of_le threads manager hlen _ (by simpa using hc')
  rw [heq] at hc''
  unfold CommentThread.linearize
  exact List.mem_map.mpr ⟨c, hc'', hcref⟩

/-- The index `nextCommentInThread` / `previousCommentInThread` compute via `idxOf` genuinely finds
`sel.comment` -- it is not the "not found" sentinel, and the entry it points at really is
`sel.comment`, not some coincidentally-earlier match. This is the "and the one that is selected"
half of `SelectedComment.WellFormed`; totality alone (`linearizedCommentRefs_ne_nil`) doesn't need
it, but genuine correctness of the selection does. -/
theorem SelectedComment.WellFormed.currentlySelectedIndex_eq {threads : CommentThreads} {sel : SelectedComment}
    (manager : CommentManager) (hCoverage : ∀ ref, threads.commentTreeNodes.contains ref → manager.comments.contains ref)
    (hWF : SelectedComment.WellFormed threads sel) :
    ∃ h : ((sel.thread.linearize threads manager).map (·.ref)).idxOf sel.comment <
        ((sel.thread.linearize threads manager).map (·.ref)).length,
      ((sel.thread.linearize threads manager).map (·.ref))[
        ((sel.thread.linearize threads manager).map (·.ref)).idxOf sel.comment] = sel.comment := by
  have hlt := List.idxOf_lt_length_of_mem (hWF.comment_mem_linearizedCommentRefs manager hCoverage)
  exact ⟨hlt, List.getElem_idxOf hlt⟩

/-- Given a selection, select the next comment in the linear order.

`hWF` certifies that `selection` is well-formed with respect to `threads`, which is what makes the
indexing into the thread's linearization provably in-bounds (see
`SelectedComment.WellFormed.linearizedCommentRefs_ne_nil`) instead of relying on a `!`-panic
fallback. -/
public def CommentThreads.nextCommentInThread (threads : CommentThreads) (manager : CommentManager)
    (selection : SelectedComment) (hWF : SelectedComment.WellFormed threads selection) : SelectedComment :=
  let selectedThread := selection.thread
  let linearizedComments := selectedThread.linearize threads manager
  let linearizedCommentRefs := linearizedComments.map (λ c => c.ref)
  let currentlySelectedRef := selection.comment
  let currentlySelectedIndex := linearizedCommentRefs.idxOf currentlySelectedRef
  let nextIdx := min (currentlySelectedIndex + 1) (linearizedCommentRefs.length - 1)
  have hNonempty : linearizedCommentRefs ≠ [] := hWF.linearizedCommentRefs_ne_nil manager
  have hBound : nextIdx < linearizedCommentRefs.length := by
    have h1 : nextIdx ≤ linearizedCommentRefs.length - 1 := Nat.min_le_right _ _
    have h2 : 0 < linearizedCommentRefs.length := List.ne_nil_iff_length_pos.mp hNonempty
    omega
  ⟨selection.version, selection.thread, linearizedCommentRefs[nextIdx]'hBound⟩


/-- Given a selection, select the previous comment in the linear order.

`hWF` certifies that `selection` is well-formed with respect to `threads`; see
`CommentThreads.nextCommentInThread` for why this makes the indexing provably in-bounds. -/
public def CommentThreads.previousCommentInThread (threads : CommentThreads) (manager : CommentManager)
    (selection : SelectedComment) (hWF : SelectedComment.WellFormed threads selection) : SelectedComment :=
  let selectedThread := selection.thread
  let linearizedComments := selectedThread.linearize threads manager
  let linearizedCommentRefs := linearizedComments.map (λ c => c.ref)
  let currentlySelectedRef := selection.comment
  let currentlySelectedIndex := linearizedCommentRefs.idxOf currentlySelectedRef
  let nextIdx := max 0 (currentlySelectedIndex - 1)
  have hNonempty : linearizedCommentRefs ≠ [] := hWF.linearizedCommentRefs_ne_nil manager
  have hEq : nextIdx = currentlySelectedIndex - 1 := Nat.max_eq_right (Nat.zero_le _)
  have hBound : nextIdx < linearizedCommentRefs.length := by
    have h2 : currentlySelectedIndex ≤ linearizedCommentRefs.length := List.idxOf_le_length
    have h3 : 0 < linearizedCommentRefs.length := List.ne_nil_iff_length_pos.mp hNonempty
    omega
  ⟨selection.version, selection.thread, linearizedCommentRefs[nextIdx]'hBound⟩


theorem CommentThreads.nextCommentInThread.selectNextIfNotLastCommentSelected
    (threads : CommentThreads) (manager : CommentManager) (selection : SelectedComment)
    (hWF : SelectedComment.WellFormed threads selection)
    (refs : List CommentRef) (idx : Nat)
    (hRefs : refs = (selection.thread.linearize threads manager).map (·.ref))
    (hIdx : refs.idxOf selection.comment = idx)
    (hNotLast : idx + 1 < refs.length) :
    threads.nextCommentInThread manager selection hWF =
      ⟨selection.version, selection.thread, refs[idx + 1]!⟩ := by
  unfold CommentThreads.nextCommentInThread
  have hNextIdxEq : Nat.min (idx + 1) (refs.length - 1) = idx + 1 := Nat.min_eq_left (by omega)
  simp only [← hRefs, hIdx, hNextIdxEq]
  congr 1
  exact (List.getElem!_of_getElem? (List.getElem?_eq_getElem hNotLast)).symm

theorem CommentThreads.nextCommentInThread.saturateIfLastCommentSelected
    (threads : CommentThreads) (manager : CommentManager) (selection : SelectedComment)
    (hWF : SelectedComment.WellFormed threads selection)
    (refs : List CommentRef) (idx : Nat)
    (hRefs : refs = (selection.thread.linearize threads manager).map (·.ref))
    (hIdx : refs.idxOf selection.comment = idx)
    (hLast : idx + 1 = refs.length) :
    threads.nextCommentInThread manager selection hWF = selection := by
  subst hIdx
  unfold CommentThreads.nextCommentInThread
  have hIdxLt : refs.idxOf selection.comment < refs.length := by omega
  have hGetElem : refs[refs.idxOf selection.comment] = selection.comment := List.getElem_idxOf hIdxLt
  have hNextIdxEq : Nat.min (refs.idxOf selection.comment + 1) (refs.length - 1) = refs.idxOf selection.comment :=
    (Nat.min_eq_right (by omega)).trans (by omega)
  obtain ⟨sv, sthread, scomment⟩ := selection
  simp only [← hRefs, hNextIdxEq] at hGetElem ⊢
  simp only [hGetElem]

theorem CommentThreads.previousCommentInThread.selectPreviousIfNotFirstCommentSelected
    (threads : CommentThreads) (manager : CommentManager) (selection : SelectedComment)
    (hWF : SelectedComment.WellFormed threads selection)
    (refs : List CommentRef) (idx : Nat)
    (hRefs : refs = (selection.thread.linearize threads manager).map (·.ref))
    (hIdx : refs.idxOf selection.comment = idx)
    (_hNotFirst : idx ≠ 0) :
    threads.previousCommentInThread manager selection hWF =
      ⟨selection.version, selection.thread, refs[idx - 1]!⟩ := by
  unfold CommentThreads.previousCommentInThread
  have hNextIdxEq : max 0 (idx - 1) = idx - 1 := Nat.max_eq_right (Nat.zero_le _)
  simp only [← hRefs, hIdx, hNextIdxEq]
  congr 1
  refine (List.getElem!_of_getElem? (List.getElem?_eq_getElem ?_)).symm

theorem CommentThreads.previousCommentInThread.saturateIfFirstCommentSelected
    (threads : CommentThreads) (manager : CommentManager) (selection : SelectedComment)
    (hWF : SelectedComment.WellFormed threads selection)
    (hCoverage : ∀ ref, threads.commentTreeNodes.contains ref → manager.comments.contains ref)
    (refs : List CommentRef) (idx : Nat)
    (hRefs : refs = (selection.thread.linearize threads manager).map (·.ref))
    (hIdx : refs.idxOf selection.comment = idx)
    (hFirst : idx = 0) :
    threads.previousCommentInThread manager selection hWF = selection := by
  subst hIdx
  unfold CommentThreads.previousCommentInThread
  have hMem : selection.comment ∈ refs := by
    rw [hRefs]; exact hWF.comment_mem_linearizedCommentRefs manager hCoverage
  have hIdxLt : refs.idxOf selection.comment < refs.length := List.idxOf_lt_length_of_mem hMem
  have hGetElem : refs[refs.idxOf selection.comment] = selection.comment := List.getElem_idxOf hIdxLt
  have hNextIdxEq : max 0 (refs.idxOf selection.comment - 1) = refs.idxOf selection.comment := by omega
  obtain ⟨sv, sthread, scomment⟩ := selection
  simp only [← hRefs, hNextIdxEq] at hGetElem ⊢
  simp only [hGetElem]

private def hasConsistentLocationsPredicate (locations : List ThreadLocation) : Prop :=
  (∀ loc, loc ∈ locations → loc.isTopLevel) ∨ (∀ loc, loc ∈ locations → !loc.isTopLevel)

theorem CommentThreads.asAlist.hasConsistentLocations (threads : CommentThreads) (manager : CommentManager) :
  hasConsistentLocationsPredicate (List.map Prod.fst (threads.asAlist manager)) := by
  have hmem : ∀ loc, loc ∈ List.map Prod.fst (threads.asAlist manager) → loc ∈ threads.locationRoots.keys := by
    intro loc hloc
    unfold CommentThreads.asAlist at hloc
    simp only [List.mem_map, List.mem_mergeSort, List.mem_attach, true_and] at hloc
    obtain ⟨a, ⟨a1, heq1⟩, heq2⟩ := hloc
    have hloceq : loc = a1.1.fst := by rw [← heq2, ← heq1]; rfl
    rw [hloceq, ← Std.HashMap.map_fst_toList_eq_keys]
    exact List.mem_map.mpr ⟨a1.1, a1.2, rfl⟩
  rcases threads.hLocationsConsistent with hc | hc
  · exact Or.inl (fun loc hloc => (hc loc (hmem loc hloc)).1)
  · exact Or.inr (fun loc hloc => by simpa using hc loc (hmem loc hloc))

private def listIsSortedPredicate [Ord α] (values : List α) : Prop :=
  match values with
  | [] => True
  | v :: rest => rest.all (λ other => (compare v other).isLE) ∧ listIsSortedPredicate rest

public def ThreadLocation.le (a b : ThreadLocation) : Bool := (compare a b).isLE

private theorem ThreadLocation.le_trans : ∀ (a b c : ThreadLocation), le a b → le b c → le a c := by
  intro a b c
  unfold le compare instOrdThreadLocation instOrdThreadLocation.ord
  rcases a <;> rcases b <;> rcases c <;> simp [Nat.isLE_compare] <;> omega

private theorem ThreadLocation.le_total : ∀ (a b : ThreadLocation), le a b || le b a := by
  intro a b
  unfold le compare instOrdThreadLocation instOrdThreadLocation.ord
  rcases a <;> rcases b <;> simp [Nat.isLE_compare] <;> omega

private theorem listIsSortedPredicate_iff_pairwise {α} [Ord α] (l : List α) :
    listIsSortedPredicate l ↔ l.Pairwise (fun a b => (compare a b).isLE = true) := by
  induction l with
  | nil => simp [listIsSortedPredicate]
  | cons a l ih => simp [listIsSortedPredicate, ih]

theorem CommentThreads.asAlist.isSortedByLocation (threads : CommentThreads) (manager : CommentManager) :
  listIsSortedPredicate (List.map Prod.fst (threads.asAlist manager)) := by
  unfold CommentThreads.asAlist
  rw [List.map_mergeSort (s := ThreadLocation.le) (by
    intro a _ b _
    unfold compareLocatedCommentThreads ThreadLocation.le compare instOrdThreadLocation instOrdThreadLocation.ord
    rcases a with ⟨aloc, athreads⟩
    rcases b with ⟨bloc, bthreads⟩
    rcases aloc <;> rcases bloc <;> simp <;> rw [Bool.eq_iff_iff] <;> simp [Nat.isLE_compare])]
  rw [listIsSortedPredicate_iff_pairwise]
  exact List.pairwise_mergeSort ThreadLocation.le_trans ThreadLocation.le_total _

private theorem nat_compareLE_trans : ∀ (a b c : Nat), (compare a b).isLE → (compare b c).isLE → (compare a c).isLE := by
  intro a b c
  simp only [Nat.isLE_compare]
  omega

private theorem nat_compareLE_total : ∀ (a b : Nat), (compare a b).isLE || (compare b a).isLE := by
  intro a b
  simp only [Nat.isLE_compare, Bool.or_eq_true]
  omega

theorem CommentThreads.asAlist.threadLocationsSortedByTimestamp (threads : CommentThreads) (manager : CommentManager) :
  ∀ threadList, threadList ∈ (List.map Prod.snd (threads.asAlist manager)) →
       listIsSortedPredicate (List.map (λ commentRef => (manager.get commentRef.value).createdTimestamp) threadList) := by
  intro threadList hthreadList
  unfold CommentThreads.asAlist at hthreadList
  simp only [List.mem_map, List.mem_mergeSort, List.mem_attach, true_and] at hthreadList
  obtain ⟨a, ⟨⟨⟨loc, threadRoots⟩, hpair⟩, heq1⟩, heq2⟩ := hthreadList
  have hthreadListEq : threadList =
      List.mergeSort
        (List.map (fun x => threads.commentTreeNodes.get x.val
            (Std.HashMap.mem_iff_contains.mpr (threads.hHasNodeForComment loc threadRoots hpair x.val x.2)))
          threadRoots.attach)
        (fun t₁ t₂ => decide ((manager.get t₁.value).createdTimestamp ≤ (manager.get t₂.value).createdTimestamp)) := by
    rw [← heq2, ← heq1]; rfl
  rw [listIsSortedPredicate_iff_pairwise, List.pairwise_map, hthreadListEq]
  refine (List.pairwise_mergeSort ?_ ?_ _).imp (fun {x y} h => ?_)
  · intro t1 t2 t3 h1 h2
    simp only [decide_eq_true_eq] at h1 h2 ⊢
    omega
  · intro t1 t2
    simp only [decide_eq_true_eq, Bool.or_eq_true]
    omega
  · rw [Nat.isLE_compare]
    simpa using h

/-- Each group of threads that `toThreadsOrdered` concatenates in (i.e. each location's thread
list from `asAlist`) occurs as a contiguous run in the result, and that run is sorted by
timestamp. -/
theorem CommentThreads.toThreadsOrdered.groupsAreSorted (threads : CommentThreads) (manager : CommentManager) :
  ∀ threadList, threadList ∈ (List.map Prod.snd (threads.asAlist manager)) →
    threadList.IsInfix (threads.toThreadsOrdered manager) ∧
    listIsSortedPredicate (List.map (λ thread => (manager.get thread.value).createdTimestamp) threadList) := by
  intro threadList hthreadList
  refine ⟨?_, CommentThreads.asAlist.threadLocationsSortedByTimestamp threads manager threadList hthreadList⟩
  obtain ⟨p, hp_mem, hp_eq⟩ := List.mem_map.mp hthreadList
  obtain ⟨s, t, hst⟩ := List.append_of_mem hp_mem
  refine ⟨List.flatMap Prod.snd s, List.flatMap Prod.snd t, ?_⟩
  unfold CommentThreads.toThreadsOrdered
  rw [hst, List.flatMap_append, List.flatMap_cons, hp_eq, List.append_assoc]

private theorem CommentThreads.toThreadsOrdered.eq_nil_of_isEmpty (threads : CommentThreads) (manager : CommentManager)
    (hEmpty : threads.isEmpty) : threads.toThreadsOrdered manager = [] := by
  have hThreadRootsEmpty : ∀ loc threadRoots, (loc, threadRoots) ∈ threads.locationRoots.toList → threadRoots = [] := by
    intro loc threadRoots hpair
    unfold CommentThreads.isEmpty at hEmpty
    rw [List.all_eq_true] at hEmpty
    simpa using hEmpty (loc, threadRoots) hpair
  unfold CommentThreads.toThreadsOrdered CommentThreads.asAlist
  rw [List.flatMap_eq_nil_iff]
  intro p hp
  simp only [List.mem_mergeSort, List.mem_map, List.mem_attach, true_and] at hp
  obtain ⟨⟨⟨loc, threadRoots⟩, hpair⟩, heq⟩ := hp
  have hRootsEmpty := hThreadRootsEmpty loc threadRoots hpair
  subst hRootsEmpty
  rw [← heq]
  simp [CommentThreads.asAlist.sortThreadLists]

theorem CommentThreads.nextThread.noSelectionForEmptyFile (threads : CommentThreads) (manager : CommentManager) (version : FileVersion) (selection : SelectedComment) :
  version ≠ selection.version ∧ threads.isEmpty → threads.nextThread manager version selection = none := by
  rintro ⟨hverne, hEmpty⟩
  have hVerNe : (version == selection.version) = false := by
    obtain ⟨sv, sthread, scomment⟩ := selection
    cases version <;> cases sv <;> simp_all <;> rfl
  unfold CommentThreads.nextThread
  rw [CommentThreads.toThreadsOrdered.eq_nil_of_isEmpty threads manager hEmpty]
  simp [hVerNe]

theorem CommentThreads.previousThread.noSelectionForEmptyFile (threads : CommentThreads) (manager : CommentManager) (version : FileVersion) (selection : SelectedComment) :
  version ≠ selection.version ∧ threads.isEmpty → threads.previousThread manager version selection = none := by
  rintro ⟨hverne, hEmpty⟩
  have hVerNe : (version == selection.version) = false := by
    obtain ⟨sv, sthread, scomment⟩ := selection
    cases version <;> cases sv <;> simp_all <;> rfl
  unfold CommentThreads.previousThread
  rw [CommentThreads.toThreadsOrdered.eq_nil_of_isEmpty threads manager hEmpty]
  simp [hVerNe]

/-- Every location's thread list contributes a matching-length group to `asAlist`'s output. -/
private theorem CommentThreads.asAlist.mem_of_locationRoots (threads : CommentThreads) (manager : CommentManager) :
    ∀ loc threadRoots, (loc, threadRoots) ∈ threads.locationRoots.toList →
      ∃ sortedThreads, (loc, sortedThreads) ∈ threads.asAlist manager ∧ sortedThreads.length = threadRoots.length := by
  intro loc threadRoots hpair
  unfold CommentThreads.asAlist
  refine ⟨_, List.mem_mergeSort.mpr (List.mem_map.mpr ⟨⟨(loc, threadRoots), hpair⟩, List.mem_attach _ _, rfl⟩), ?_⟩
  simp

private theorem CommentThreads.toThreadsOrdered.isEmpty_of_eq_nil (threads : CommentThreads) (manager : CommentManager)
    (hNil : threads.toThreadsOrdered manager = []) : threads.isEmpty := by
  unfold CommentThreads.isEmpty
  rw [List.all_eq_true]
  rintro ⟨loc, threadRoots⟩ hpair
  obtain ⟨sortedThreads, hmem, hlen⟩ := CommentThreads.asAlist.mem_of_locationRoots threads manager loc threadRoots hpair
  unfold CommentThreads.toThreadsOrdered at hNil
  rw [List.flatMap_eq_nil_iff] at hNil
  have hsnil := hNil (loc, sortedThreads) hmem
  simp only at hsnil
  rw [hsnil, List.length_nil] at hlen
  simp only [List.isEmpty_iff_length_eq_zero]
  omega

private theorem CommentThreads.toThreadsOrdered.ne_nil_of_not_isEmpty (threads : CommentThreads) (manager : CommentManager)
    (hNonEmpty : ¬ threads.isEmpty) : threads.toThreadsOrdered manager ≠ [] := by
  intro hNil
  exact hNonEmpty (CommentThreads.toThreadsOrdered.isEmpty_of_eq_nil threads manager hNil)

theorem CommentThreads.nextThread.selectFirstForDifferentFile (threads : CommentThreads) (manager : CommentManager) (version : FileVersion) (selection : SelectedComment) :
  version ≠ selection.version ∧ ¬ threads.isEmpty →
    ∃ thread, (threads.toThreadsOrdered manager).head? = some thread ∧
              threads.nextThread manager version selection = some ⟨version, thread, thread.value⟩ := by
  rintro ⟨hverne, hNonEmpty⟩
  have hVerNe : (version == selection.version) = false := by
    obtain ⟨sv, sthread, scomment⟩ := selection
    cases version <;> cases sv <;> simp_all <;> rfl
  have hNeNil : threads.toThreadsOrdered manager ≠ [] :=
    CommentThreads.toThreadsOrdered.ne_nil_of_not_isEmpty threads manager hNonEmpty
  unfold CommentThreads.nextThread
  match hmatch : threads.toThreadsOrdered manager with
  | [] => exact absurd hmatch hNeNil
  | firstThread :: rest =>
    exact ⟨firstThread, by simp, by simp [hVerNe]⟩

theorem CommentThreads.previousThread.selectLastForDifferentFile (threads : CommentThreads) (manager : CommentManager) (version : FileVersion) (selection : SelectedComment) :
  version ≠ selection.version ∧ ¬ threads.isEmpty →
    ∃ thread, (threads.toThreadsOrdered manager).getLast? = some thread ∧
              threads.previousThread manager version selection = some ⟨version, thread, thread.value⟩ := by
  rintro ⟨hverne, hNonEmpty⟩
  have hVerNe : (version == selection.version) = false := by
    obtain ⟨sv, sthread, scomment⟩ := selection
    cases version <;> cases sv <;> simp_all <;> rfl
  have hNeNil : threads.toThreadsOrdered manager ≠ [] :=
    CommentThreads.toThreadsOrdered.ne_nil_of_not_isEmpty threads manager hNonEmpty
  unfold CommentThreads.previousThread
  match hmatch : threads.toThreadsOrdered manager with
  | [] => exact absurd hmatch hNeNil
  | a :: as =>
    exact ⟨(a :: as).getLast (List.cons_ne_nil a as),
      List.getLast?_eq_some_getLast (List.cons_ne_nil a as), by simp [hVerNe]⟩

private theorem List.perm_flatMap_of_forall_perm {α β} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, List.Perm (f x) (g x)) : List.Perm (l.flatMap f) (l.flatMap g) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons]
    exact (h a List.mem_cons_self).append (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

private theorem CommentThreads.asAlist.flatMap_valueMap_perm (threads : CommentThreads) (manager : CommentManager) :
    List.Perm ((threads.asAlist manager).flatMap (fun p => p.snd.map (·.value)))
      (threads.locationRoots.toList.flatMap Prod.snd) := by
  unfold CommentThreads.asAlist
  refine (List.Perm.flatMap_right _ (List.mergeSort_perm _ _)).trans ?_
  rw [List.flatMap_map]
  refine (List.perm_flatMap_of_forall_perm (l := threads.locationRoots.toList.attach)
      (g := fun x => x.1.2) ?_).trans ?_
  · rintro ⟨⟨loc, threadRoots⟩, hpair⟩ -
    dsimp only
    refine ((List.mergeSort_perm _ _).map (fun t : CommentThread => t.value)).trans ?_
    rw [List.map_map]
    have heq : (fun t : CommentThread => t.value) ∘ (fun x : {r // r ∈ threadRoots} =>
        threads.commentTreeNodes.get x.1
          (Std.HashMap.mem_iff_contains.mpr (threads.hHasNodeForComment loc threadRoots hpair x.1 x.2))) =
        (fun x : {r // r ∈ threadRoots} => x.1) := by
      funext x
      exact threads.hCommentTreeNodeRootMatchesKey x.1 _
    rw [heq, List.attach_map_subtype_val]
  · have heq2 : (threads.locationRoots.toList.attach.flatMap (fun x => x.1.2)) =
        threads.locationRoots.toList.flatMap Prod.snd := by
      rw [List.flatMap_subtype (f := fun x : {p : ThreadLocation × List CommentRef //
          p ∈ threads.locationRoots.toList} => x.1.2) (g := Prod.snd) (fun x h => rfl)]
      rw [List.unattach_attach]
    rw [heq2]

private theorem CommentThreads.toThreadsOrdered.nodupValues (threads : CommentThreads) (manager : CommentManager) :
    ((threads.toThreadsOrdered manager).map (fun t : CommentThread => t.value)).Nodup := by
  unfold CommentThreads.toThreadsOrdered
  rw [List.map_flatMap]
  exact (CommentThreads.asAlist.flatMap_valueMap_perm threads manager).nodup_iff.mpr
    threads.hLocationRootsNodup

/-- `findIdx?` on the value predicate always recovers the index it was asked about: since
`.value`s are `Nodup` across `toThreadsOrdered`, no earlier element can also match. -/
private theorem CommentThreads.toThreadsOrdered.findIdx_of_getElem (threads : CommentThreads) (manager : CommentManager)
    {i : Nat} (hi : i < (threads.toThreadsOrdered manager).length) :
    (threads.toThreadsOrdered manager).findIdx? (fun t => t.value == (threads.toThreadsOrdered manager)[i].value) =
      some i := by
  have hNodup := CommentThreads.toThreadsOrdered.nodupValues threads manager
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨hi, by simp, fun j hji hp => ?_⟩
  have hveq : (threads.toThreadsOrdered manager)[j].value = (threads.toThreadsOrdered manager)[i].value :=
    beq_iff_eq.mp hp
  have h1 : ((threads.toThreadsOrdered manager).map (fun t => t.value))[j]? =
      ((threads.toThreadsOrdered manager).map (fun t => t.value))[i]? := by
    rw [List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem (Nat.lt_trans hji hi),
      List.getElem?_eq_getElem hi]
    simp [hveq]
  have hji' := (List.getElem?_inj (l := (threads.toThreadsOrdered manager).map (fun t => t.value))
      (by rw [List.length_map]; exact Nat.lt_trans hji hi) hNodup).mp h1
  omega

theorem CommentThreads.nextThread.saturateIfLastThreadSelected (threads : CommentThreads) (manager : CommentManager) (version : FileVersion) (selection₀ : SelectedComment) :
  (version = selection₀.version ∧ ¬ threads.isEmpty ∧ ∃ thread, (threads.toThreadsOrdered manager).getLast? = some thread ∧ selection₀.thread = thread) →
     ∃ selection₁, threads.nextThread manager version selection₀ = some selection₁ ∧ selection₀.thread = selection₁.thread := by
  rintro ⟨hver, -, thread, hLast, hSelEq⟩
  have hVerEq : (version == selection₀.version) = true := by
    subst hver
    cases selection₀.version <;> rfl
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hLast
  have hNodup := CommentThreads.toThreadsOrdered.nodupValues threads manager
  rw [hys, List.map_append, List.map_cons, List.map_nil, List.nodup_append] at hNodup
  obtain ⟨-, -, hdisj⟩ := hNodup
  have hNotMemVal : ∀ y ∈ ys, y.value ≠ thread.value := by
    intro y hy
    exact hdisj y.value (List.mem_map_of_mem hy) thread.value (List.mem_singleton_self thread.value)
  have hFindIdx : (threads.toThreadsOrdered manager).findIdx? (fun t => t.value == selection₀.thread.value) = some ys.length := by
    rw [hSelEq, hys, List.findIdx?_append]
    have hNone : ys.findIdx? (fun t => t.value == thread.value) = none := by
      rw [List.findIdx?_eq_none_iff]
      intro x hx
      exact beq_eq_false_iff_ne.mpr (hNotMemVal x hx)
    simp [hNone]
  have hLenEq : (threads.toThreadsOrdered manager).length = ys.length + 1 := by
    rw [hys]; simp
  have hNextIdxEq : Nat.min (ys.length + 1) ((threads.toThreadsOrdered manager).length - 1) = ys.length := by
    rw [hLenEq]; simp
  have hGetElem : (threads.toThreadsOrdered manager)[ys.length]! = thread := by
    apply List.getElem!_of_getElem?
    rw [hys]
    exact List.getElem?_concat_length
  refine ⟨⟨version, thread, thread.value⟩, ?_, by simpa using hSelEq⟩
  unfold CommentThreads.nextThread
  simp only [hVerEq, hFindIdx, hNextIdxEq, hGetElem]

theorem CommentThreads.previousThread.saturateIfFirstThreadSelected (threads : CommentThreads) (manager : CommentManager) (version : FileVersion) (selection₀ : SelectedComment) :
  (version = selection₀.version ∧ ¬ threads.isEmpty ∧ ∃ thread, (threads.toThreadsOrdered manager).head? = some thread ∧ selection₀.thread = thread) →
     ∃ selection₁, threads.previousThread manager version selection₀ = some selection₁ ∧ selection₀.thread = selection₁.thread := by
  rintro ⟨hver, -, thread, hHead, hSelEq⟩
  have hVerEq : (version == selection₀.version) = true := by
    subst hver
    cases selection₀.version <;> rfl
  obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp hHead
  have hFindIdx : (threads.toThreadsOrdered manager).findIdx? (fun t => t.value == selection₀.thread.value) = some 0 := by
    rw [hSelEq, hys]
    simp [List.findIdx?_cons]
  have hGetElem : (threads.toThreadsOrdered manager)[0]! = thread := by
    apply List.getElem!_of_getElem?
    rw [hys]
    simp
  refine ⟨⟨version, thread, thread.value⟩, ?_, by simpa using hSelEq⟩
  unfold CommentThreads.previousThread
  simp only [hVerEq, hFindIdx, hGetElem, beq_self_eq_true, if_true]

theorem CommentThreads.nextThread.selectNextIfNotLastThreadSelected (threads : CommentThreads) (manager : CommentManager) (version : FileVersion) (selection₀ : SelectedComment) :
  (version = selection₀.version ∧ ¬ threads.isEmpty ∧
    (∃ idx₀, List.findIdx? (·.value == selection₀.thread.value) (threads.toThreadsOrdered manager) = some idx₀) ∧
    ∃ thread, (threads.toThreadsOrdered manager).getLast? = some thread ∧ selection₀.thread.value ≠ thread.value) →
     (∃ selection₁, threads.nextThread manager version selection₀ = some selection₁ ∧
      ∃ idx₀ idx₁, List.findIdx? (·.value == selection₀.thread.value) (threads.toThreadsOrdered manager) = some idx₀ ∧
                   List.findIdx? (·.value == selection₁.thread.value) (threads.toThreadsOrdered manager) = some idx₁ ∧
                   idx₀ + 1 = idx₁) := by
  rintro ⟨hver, -, ⟨idx₀, hFindIdx₀⟩, lastThread, hLast, hNeVal⟩
  have hVerEq : (version == selection₀.version) = true := by
    subst hver
    cases selection₀.version <;> rfl
  have hNodup := CommentThreads.toThreadsOrdered.nodupValues threads manager
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hLast
  have hLenEq : (threads.toThreadsOrdered manager).length = ys.length + 1 := by
    rw [hys]; simp
  obtain ⟨hIdx₀Lt, hIdx₀P, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hFindIdx₀
  have hGetElem₀Val : (threads.toThreadsOrdered manager)[idx₀].value = selection₀.thread.value :=
    beq_iff_eq.mp hIdx₀P
  have hLastElem : (threads.toThreadsOrdered manager)[ys.length]! = lastThread := by
    apply List.getElem!_of_getElem?
    rw [hys]
    exact List.getElem?_concat_length
  have hIdx₀Ne : idx₀ ≠ ys.length := by
    intro heq
    apply hNeVal
    have h1 : (threads.toThreadsOrdered manager)[idx₀]? = some lastThread := by
      rw [heq, hys]
      exact List.getElem?_concat_length
    rw [List.getElem?_eq_getElem hIdx₀Lt] at h1
    rw [← hGetElem₀Val]
    exact congrArg Tree.value (Option.some.inj h1)
  have hIdx₀LtYs : idx₀ < ys.length := by
    rw [hLenEq] at hIdx₀Lt
    omega
  have hNextIdxEq : Nat.min (idx₀ + 1) ((threads.toThreadsOrdered manager).length - 1) = idx₀ + 1 := by
    rw [hLenEq]
    exact Nat.min_eq_left (by omega)
  have hIdx₁Lt : idx₀ + 1 < (threads.toThreadsOrdered manager).length := by
    rw [hLenEq]; omega
  have hGetElem₁ : (threads.toThreadsOrdered manager)[idx₀ + 1]! = (threads.toThreadsOrdered manager)[idx₀ + 1] :=
    List.getElem!_of_getElem? (List.getElem?_eq_getElem hIdx₁Lt)
  have hFindIdx₁ := CommentThreads.toThreadsOrdered.findIdx_of_getElem threads manager hIdx₁Lt
  refine ⟨⟨version, (threads.toThreadsOrdered manager)[idx₀ + 1], (threads.toThreadsOrdered manager)[idx₀ + 1].value⟩,
    ?_, idx₀, idx₀ + 1, hFindIdx₀, ?_, rfl⟩
  · unfold CommentThreads.nextThread
    simp only [hVerEq, hFindIdx₀, hNextIdxEq, hGetElem₁]
  · simpa using hFindIdx₁

theorem CommentThreads.previousThread.selectPreviousIfNotFirstThreadSelected (threads : CommentThreads) (manager : CommentManager) (version : FileVersion) (selection₀ : SelectedComment) :
  (version = selection₀.version ∧ ¬ threads.isEmpty ∧
    (∃ idx₀, List.findIdx? (·.value == selection₀.thread.value) (threads.toThreadsOrdered manager) = some idx₀) ∧
    ∃ thread, (threads.toThreadsOrdered manager).head? = some thread ∧ selection₀.thread.value ≠ thread.value) →
     (∃ selection₁, threads.previousThread manager version selection₀ = some selection₁ ∧
      ∃ idx₀ idx₁, List.findIdx? (·.value == selection₀.thread.value) (threads.toThreadsOrdered manager) = some idx₀ ∧
                   List.findIdx? (·.value == selection₁.thread.value) (threads.toThreadsOrdered manager) = some idx₁ ∧
                   idx₀ - 1 = idx₁) := by
  rintro ⟨hver, -, ⟨idx₀, hFindIdx₀⟩, firstThread, hHead, hNeVal⟩
  have hVerEq : (version == selection₀.version) = true := by
    subst hver
    cases selection₀.version <;> rfl
  obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp hHead
  obtain ⟨hIdx₀Lt, hIdx₀P, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hFindIdx₀
  have hGetElem₀Val : (threads.toThreadsOrdered manager)[idx₀].value = selection₀.thread.value :=
    beq_iff_eq.mp hIdx₀P
  have hFirstElem : (threads.toThreadsOrdered manager)[0]! = firstThread := by
    apply List.getElem!_of_getElem?
    rw [hys]
    simp
  have hIdx₀Ne : idx₀ ≠ 0 := by
    intro heq
    apply hNeVal
    have h1 : (threads.toThreadsOrdered manager)[idx₀]? = some firstThread := by
      rw [heq, hys]
      simp
    rw [List.getElem?_eq_getElem hIdx₀Lt] at h1
    rw [← hGetElem₀Val]
    exact congrArg Tree.value (Option.some.inj h1)
  have hPrevIdxEq : (if idx₀ == 0 then 0 else idx₀ - 1) = idx₀ - 1 := by
    have hFalse : (idx₀ == 0) = false := by simpa using hIdx₀Ne
    simp [hFalse]
  have hIdx₁Lt : idx₀ - 1 < (threads.toThreadsOrdered manager).length := by omega
  have hGetElem₁ : (threads.toThreadsOrdered manager)[idx₀ - 1]! = (threads.toThreadsOrdered manager)[idx₀ - 1] :=
    List.getElem!_of_getElem? (List.getElem?_eq_getElem hIdx₁Lt)
  have hFindIdx₁ := CommentThreads.toThreadsOrdered.findIdx_of_getElem threads manager hIdx₁Lt
  refine ⟨⟨version, (threads.toThreadsOrdered manager)[idx₀ - 1], (threads.toThreadsOrdered manager)[idx₀ - 1].value⟩,
    ?_, idx₀, idx₀ - 1, hFindIdx₀, ?_, rfl⟩
  · unfold CommentThreads.previousThread
    simp only [hVerEq, hFindIdx₀, hPrevIdxEq, hGetElem₁]
  · simpa using hFindIdx₁
