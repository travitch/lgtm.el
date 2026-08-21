module

import all LgtmLean.Basic

/-- Extract an alist of threads grouped by location.

The list is sorted by location.  Each list at a given location is sorted by comment timestamp.
The comment manager is required to get access to those timestamps. -/
def CommentThreads.asAlist (threads : CommentThreads) (manager : CommentManager) : List (ThreadLocation × List CommentThread) :=
  let unsorted := threads.locationRoots.toList.attach.map (λ ⟨(loc, threadRoots), hpair⟩ =>
    let commentThreads := threadRoots.attach.map (λ ⟨commentRef, href⟩ =>
      let hMember := Std.HashMap.mem_iff_contains.mpr (threads.hHasNodeForComment loc threadRoots hpair commentRef href)
      threads.commentTreeNodes.get commentRef hMember)
    let sortByComparison := λ t1 t2 => (compare (manager.get t1.value).createdTimestamp (manager.get t2.value).createdTimestamp).isLE
    let sortedThreads := List.mergeSort commentThreads sortByComparison
    (loc, sortedThreads))
  unsorted.mergeSort (λ p1 p2 => (compare p1.fst p2.fst).isLE)

/-- Return the threads in sorted order. -/
def CommentThreads.toThreadsOrdered (threads : CommentThreads) (manager : CommentManager) : List CommentThread :=
  List.flatMap (λ p => Prod.snd p) (threads.asAlist manager)

/--
Given a collection of threads and a selection, return the next thread to select linearly.

The VERSION is included because the user can switch files; as there is only one global selection,
if the user selects the next comment in a different file, the whole selection resets.

The linear order is as established in the ordering defined by CommentThreads.

Note: It would be nice to keep the association between the selection and the threads objects it references.  Future work.
-/
def CommentThreads.nextThread (threads : CommentThreads) (manager : CommentManager) (version : FileVersion) (selection : SelectedComment) : Option SelectedComment :=
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

def CommentThreads.previousThread (threads : CommentThreads) (manager : CommentManager) (version : FileVersion) (selection : SelectedComment) : Option SelectedComment :=
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


private def hasConsistentLocationsPredicate (locations : List ThreadLocation) : Prop :=
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
