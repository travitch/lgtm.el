module

import all LgtmLean.Basic

/-- Extract an alist of threads grouped by location.

The list is sorted by location.  Each list at a given location is sorted by comment timestamp.
The comment manager is required to get access to those timestamps. -/
private def CommentThreads.asAlist (threads : CommentThreads) (manager : CommentManager) : List (ThreadLocation × List CommentThread) :=
  let unsorted := threads.locationRoots.toList.attach.map (λ ⟨(loc, threadRoots), hpair⟩ =>
    let commentThreads := threadRoots.attach.map (λ ⟨commentRef, href⟩ =>
      let hMember := Std.HashMap.mem_iff_contains.mpr (threads.hHasNodeForComment loc threadRoots hpair commentRef href)
      threads.commentTreeNodes.get commentRef hMember)
    let sortByComparison := λ t1 t2 => (compare (manager.get t1.value).createdTimestamp (manager.get t2.value).createdTimestamp).isLE
    let sortedThreads := List.mergeSort commentThreads sortByComparison
    (loc, sortedThreads))
  unsorted.mergeSort (λ p1 p2 => (compare p1.fst p2.fst).isLE)

def hasConsistentLocationsPredicate (locations : List ThreadLocation) : Prop :=
  (∀ loc, loc ∈ locations → loc.isTopLevel) ∨ (∀ loc, loc ∈ locations → !loc.isTopLevel)

theorem CommentThreads.asAlist.hasConsistentLocations (threads : CommentThreads) (manager : CommentManager) :
  hasConsistentLocationsPredicate (List.map Prod.fst (threads.asAlist manager)) := by
  have hmem : ∀ loc, loc ∈ List.map Prod.fst (threads.asAlist manager) → loc ∈ threads.locationRoots.keys := by
    intro loc hloc
    unfold CommentThreads.asAlist at hloc
    simp only [List.mem_map, List.mem_mergeSort, List.mem_attach, true_and] at hloc
    obtain ⟨a, ⟨a1, heq1⟩, heq2⟩ := hloc
    have hloceq : loc = a1.1.fst := by rw [← heq2, ← heq1]
    rw [hloceq, ← Std.HashMap.map_fst_toList_eq_keys]
    exact List.mem_map.mpr ⟨a1.1, a1.2, rfl⟩
  rcases threads.hLocationsConsistent with hc | hc
  · exact Or.inl (fun loc hloc => (hc loc (hmem loc hloc)).1)
  · exact Or.inr (fun loc hloc => by simpa using hc loc (hmem loc hloc))

private def listIsSortedPredicate [Ord α] (values : List α) : Prop :=
  match values with
  | [] => True
  | v :: rest => rest.all (λ other => (compare v other).isLE) ∧ listIsSortedPredicate rest

private def ThreadLocation.le (a b : ThreadLocation) : Bool := (compare a b).isLE

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
  rw [List.map_mergeSort (s := ThreadLocation.le) (by intro a _ b _; rfl)]
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
        (fun t1 t2 => (compare (manager.get t1.value).createdTimestamp (manager.get t2.value).createdTimestamp).isLE) := by
    rw [← heq2, ← heq1]
  rw [listIsSortedPredicate_iff_pairwise, List.pairwise_map, hthreadListEq]
  refine (List.pairwise_mergeSort ?_ ?_ _).imp (fun {x y} h => ?_)
  · intro t1 t2 t3 h1 h2
    exact nat_compareLE_trans _ _ _ h1 h2
  · intro t1 t2
    exact nat_compareLE_total _ _
  · exact h


/-- Return the threads in sorted order. -/
private def CommentThreads.toThreadsOrdered (threads : CommentThreads) (manager : CommentManager) : List CommentThread :=
  List.flatMap (λ p => Prod.snd p) (threads.asAlist manager)

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

/--
Given a collection of threads and a selection, return the next thread to select linearly.

The VERSION is included because the user can switch files; as there is only one global selection,
if the user selects the next comment in a different file, the whole selection resets.

The linear order is as established in the ordering defined by CommentThreads.

Note: It would be nice to keep the association between the selection and the threads objects it references.  Future work.
-/
private def CommentThreads.nextThread (threads : CommentThreads) (manager : CommentManager) (version : FileVersion) (selection : SelectedComment) : Option SelectedComment :=
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
  simp

theorem CommentThreads.nextThread.noSelectionForEmptyFile (threads : CommentThreads) (manager : CommentManager) (version : FileVersion) (selection : SelectedComment) :
  version ≠ selection.version ∧ threads.isEmpty → threads.nextThread manager version selection = none := by
  rintro ⟨hverne, hEmpty⟩
  have hVerNe : (version == selection.version) = false := by
    obtain ⟨sv, sthread, scomment⟩ := selection
    cases version <;> cases sv <;> simp_all <;> rfl
  unfold CommentThreads.nextThread
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

/- theorem CommentThreads.nextThread.saturateIfLastThreadSelected (threads : CommentThreads) (manager : CommentManager) (version : FileVersion) (selection : SelectedComment) :
 -   version = selection.version ∧ ∃ idx, -/
