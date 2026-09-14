import Std
import Extractor.Render

/-- The number of `constantNames` not yet in `visiting`. Used only as the termination measure for
`visitConstantForTopoSort`/`visitConstantsForTopoSort`: visiting a new name (one drawn from
`constantNames` and not already in `visiting`) strictly shrinks this, which is what
`remaining_insert_lt` below establishes. -/
private def remaining (constantNames visiting : Std.HashSet String) : Nat :=
  (constantNames.toList.filter (fun n => !visiting.contains n)).length

private theorem remaining_insert_lt (constantNames visiting : Std.HashSet String) (name : String)
    (hMem : name ∈ constantNames) (hNotVisiting : ¬ visiting.contains name) :
    remaining constantNames (visiting.insert name) < remaining constantNames visiting := by
  unfold remaining
  have hEq : (constantNames.toList.filter (fun n => !(visiting.insert name).contains n))
      = (constantNames.toList.filter (fun n => !visiting.contains n)).filter (fun n => !(name == n)) := by
    rw [List.filter_filter]
    congr 1
    funext n
    simp [Std.HashSet.contains_insert, Bool.not_or]
  rw [hEq, List.length_filter_lt_length_iff_exists]
  refine ⟨name, ?_, ?_⟩
  · rw [List.mem_filter]
    exact ⟨Std.HashSet.mem_toList.mpr hMem, by simp [hNotVisiting]⟩
  · simp

mutual

/-- Depth-first, postorder visit of `name` in the dependency graph implied by `calledGlobalNames`,
restricted to edges landing on another constant (a reference to an ordinary function doesn't
constrain ordering, since a `defun` body isn't evaluated until it's called, unlike a `defconst`
initializer). Appends every dependency to `acc` before `name` itself, so nothing ever precedes
something it depends on; `visited` (threaded across the whole traversal) keeps each constant from
being emitted twice, while `visiting` (reset per top-level start, extended going down) tracks the
current path so a genuine dependency cycle -- which shouldn't arise for well-formed top-level
`LgtmLean` constants, since a Lean `def`'s value can only reference declarations that already exist
-- gets silently broken rather than looping forever.

The `constantNames.contains name` guard is a no-op for every real caller (both `sortConstantsTopologically`
and the recursive call below only ever pass a `name` drawn from `constantNames`), added solely so
the termination measure (`remaining`, strictly decreasing on every genuine visit) is total and
provable without threading an extra membership hypothesis through the signature. -/
private def visitConstantForTopoSort (calledGlobalNames : Std.HashMap String (Std.HashSet String))
    (constantNames : Std.HashSet String) (name : String) (visiting : Std.HashSet String)
    (visited : Std.HashSet String) (acc : List String) : Std.HashSet String × List String :=
  if _hcn : constantNames.contains name then
    if _hvv : visited.contains name || visiting.contains name then
      (visited, acc)
    else
      let deps := (calledGlobalNames.getD name Std.HashSet.emptyWithCapacity).toList.filter constantNames.contains
      let (visited', acc') :=
        visitConstantsForTopoSort calledGlobalNames constantNames deps (visiting.insert name) visited acc
      (visited'.insert name, acc' ++ [name])
  else
    (visited, acc)
termination_by (remaining constantNames visiting, 0)
decreasing_by
  simp only [Bool.or_eq_true, not_or] at _hvv
  have hMem : name ∈ constantNames := Std.HashSet.mem_iff_contains.mpr _hcn
  have hNotVisiting : ¬ visiting.contains name := by simpa using _hvv.2
  have := remaining_insert_lt constantNames visiting name hMem hNotVisiting
  simp_all
  omega

/-- Visit each dependency in `deps` in turn (threading `visited`/`acc` through), the list-recursive
half of `visitConstantForTopoSort`'s mutual recursion -- broken out as its own function (rather than
a `List.foldl`) purely so Lean's termination checker can see the recursive calls directly. -/
private def visitConstantsForTopoSort (calledGlobalNames : Std.HashMap String (Std.HashSet String))
    (constantNames : Std.HashSet String) (deps : List String) (visiting : Std.HashSet String)
    (visited : Std.HashSet String) (acc : List String) : Std.HashSet String × List String :=
  match deps with
  | [] => (visited, acc)
  | dep :: rest =>
    let (visited', acc') := visitConstantForTopoSort calledGlobalNames constantNames dep visiting visited acc
    visitConstantsForTopoSort calledGlobalNames constantNames rest visiting visited' acc'
termination_by (remaining constantNames visiting, deps.length)
decreasing_by
  all_goals simp_all; omega

end

/-- Use the `calledGlobalNames` field of `postTranslationState` to topologially sort the list of constants.

Several constant initializers refer to other constants in their initializers.  Constants in elisp
must be defined before they are referenced.  `calledGlobalNames` records which constant initializer
refers to which other constants.

-/
def sortConstantsTopologically (postTranslationState : SExprState) (constants : List (String × SExpr)) :
    List (String × SExpr) :=
  let constantMap : Std.HashMap String SExpr :=
    constants.foldl (fun m (name, sexpr) => m.insert name sexpr) Std.HashMap.emptyWithCapacity
  let constantNames : Std.HashSet String :=
    constants.foldl (fun s (name, _) => s.insert name) Std.HashSet.emptyWithCapacity
  let (_, orderedNames) := constants.foldl
    (fun (visited, acc) (name, _) =>
      visitConstantForTopoSort postTranslationState.calledGlobalNames constantNames name
        Std.HashSet.emptyWithCapacity visited acc)
    (Std.HashSet.emptyWithCapacity, [])
  orderedNames.filterMap (fun name => (constantMap[name]?).map (name, ·))

private def indexOfConstant (constantName : String) (sortedList : List (String × α)) : Nat :=
  sortedList.findIdx (·.1 == constantName)

/-- `visited.contains x` and `x ∈ acc` agree for every `x`, and `acc` has no duplicates. The
correctness proof threads this through the whole traversal: it's what lets a `visited.contains`
fact (cheap, from a later call's own guard) be converted into an `acc`-membership fact (what we
actually need to reason about position), and back. -/
private def AccInv (visited : Std.HashSet String) (acc : List String) : Prop :=
  (∀ x, visited.contains x ↔ x ∈ acc) ∧ acc.Nodup

section
variable (calledGlobalNames : Std.HashMap String (Std.HashSet String)) (constantNames : Std.HashSet String)
  (rank : String → Nat)
  (hRankEdge : ∀ a b, constantNames.contains a = true → constantNames.contains b = true →
    b ∈ calledGlobalNames.getD a Std.HashSet.emptyWithCapacity → rank b < rank a)

private def filteredDeps (name : String) : List String :=
  (calledGlobalNames.getD name Std.HashSet.emptyWithCapacity).toList.filter constantNames.contains

/-- `d` has already been placed into `acc` at a position with a documented "before" witness: some
prefix `pre` of `acc` already contains every filtered dependency of `d`, without yet containing `d`
itself. Combined with `d ∈ acc`, this is exactly the fact `sortConstantsTopologically.isCorrect`
needs -- `d`'s dependencies precede it -- stated so it can be *carried forward* as `acc` grows
(see `WellPlaced_mono`) rather than re-derived every time. -/
private def WellPlaced (acc : List String) (d : String) : Prop :=
  d ∈ acc ∧ ∃ pre, pre <+: acc ∧ d ∉ pre ∧ ∀ dep ∈ filteredDeps calledGlobalNames constantNames d, dep ∈ pre

/-- `WellPlaced` survives `acc` growing by any prefix-preserving extension: the same "before"
witness `pre` still works against the longer list. This is what lets a name's placement, once
established, remain valid through however much further processing happens afterward -- the crux of
threading it as an ongoing invariant instead of a one-shot fact. -/
private theorem WellPlaced_mono (acc acc' : List String) (hpre : acc <+: acc') (d : String)
    (h : WellPlaced calledGlobalNames constantNames acc d) : WellPlaced calledGlobalNames constantNames acc' d := by
  obtain ⟨hmem, pre, hpreLe, hnotmem, hdeps⟩ := h
  exact ⟨hpre.mem hmem, pre, hpreLe.trans hpre, hnotmem, hdeps⟩

/-- The invariant carried through `visitConstantForTopoSort`'s well-founded recursion (paired with
`motive2` below for `visitConstantsForTopoSort`), proved via `visitConstantForTopoSort.induct`.
Beyond `AccInv`/prefix-monotonicity/frozen-visiting (mirroring the plain termination-measure
argument), the two invariants that make the final correctness theorem provable are:
- `rank name ≤ rank n` for every `n` currently `visiting`: since every edge strictly decreases
  rank (`hRankEdge`), this rules out a filtered dependency ever being a currently-active ancestor
  -- the one scenario that would otherwise stop it from getting placed before `name`.
- the last conjunct: a real (non-skipped) visit leaves `name` itself `WellPlaced`, and every
  already-visited name stays `WellPlaced` (via `WellPlaced_mono` against this call's own prefix
  growth) -- so nothing already placed is ever "un-placed" by later processing. -/
private def motive1 (name : String) (visiting visited : Std.HashSet String) (acc : List String) : Prop :=
  AccInv visited acc → (∀ n, visiting.contains n = true → rank name ≤ rank n) →
  (∀ d, visited.contains d = true → WellPlaced calledGlobalNames constantNames acc d) →
  AccInv (visitConstantForTopoSort calledGlobalNames constantNames name visiting visited acc).1
         (visitConstantForTopoSort calledGlobalNames constantNames name visiting visited acc).2 ∧
  acc <+: (visitConstantForTopoSort calledGlobalNames constantNames name visiting visited acc).2 ∧
  (∀ y, visiting.contains y = true →
     (visitConstantForTopoSort calledGlobalNames constantNames name visiting visited acc).1.contains y = visited.contains y) ∧
  (∀ d, (visitConstantForTopoSort calledGlobalNames constantNames name visiting visited acc).1.contains d = true →
     WellPlaced calledGlobalNames constantNames
       (visitConstantForTopoSort calledGlobalNames constantNames name visiting visited acc).2 d) ∧
  (constantNames.contains name = true → visiting.contains name = false →
     (visitConstantForTopoSort calledGlobalNames constantNames name visiting visited acc).1.contains name = true)

/-- The `visitConstantsForTopoSort` (list-processing) counterpart of `motive1`. `boundRank` bounds
every element of `deps` (all filtered dependencies of some common caller), which is what lets each
recursive visit re-derive its own `rank`-vs-`visiting` invariant from this one. -/
private def motive2 (deps : List String) (visiting visited : Std.HashSet String) (acc : List String) : Prop :=
  ∀ boundRank : Nat, (∀ d ∈ deps, constantNames.contains d = true) → (∀ d ∈ deps, rank d < boundRank) →
    (∀ n, visiting.contains n = true → boundRank ≤ rank n) → AccInv visited acc →
    (∀ d, visited.contains d = true → WellPlaced calledGlobalNames constantNames acc d) →
  AccInv (visitConstantsForTopoSort calledGlobalNames constantNames deps visiting visited acc).1
         (visitConstantsForTopoSort calledGlobalNames constantNames deps visiting visited acc).2 ∧
  acc <+: (visitConstantsForTopoSort calledGlobalNames constantNames deps visiting visited acc).2 ∧
  (∀ y, visiting.contains y = true →
     (visitConstantsForTopoSort calledGlobalNames constantNames deps visiting visited acc).1.contains y = visited.contains y) ∧
  (∀ d, (visitConstantsForTopoSort calledGlobalNames constantNames deps visiting visited acc).1.contains d = true →
     WellPlaced calledGlobalNames constantNames
       (visitConstantsForTopoSort calledGlobalNames constantNames deps visiting visited acc).2 d) ∧
  (∀ d ∈ deps, (visitConstantsForTopoSort calledGlobalNames constantNames deps visiting visited acc).1.contains d = true)

private theorem topoCase1 : ∀ (name : String) (visiting visited : Std.HashSet String) (acc : List String),
    constantNames.contains name = true →
      (visited.contains name || visiting.contains name) = true →
        motive1 calledGlobalNames constantNames rank name visiting visited acc := by
  intro name visiting visited acc hcn hvv hInv _hRV hWP
  rw [visitConstantForTopoSort.eq_1]
  simp only [hcn, hvv]
  refine ⟨hInv, List.prefix_refl acc, fun _ _ => rfl, hWP, ?_⟩
  intro _ hvisiting
  rw [Bool.or_eq_true] at hvv
  rcases hvv with h | h
  · exact h
  · simp [h] at hvisiting

include hRankEdge in
private theorem topoCase2 : ∀ (name : String) (visiting visited : Std.HashSet String) (acc : List String),
    constantNames.contains name = true →
      ¬(visited.contains name || visiting.contains name) = true →
        ∀ (visited' : Std.HashSet String) (acc' : List String),
          visitConstantsForTopoSort calledGlobalNames constantNames
            (filteredDeps calledGlobalNames constantNames name)
            (visiting.insert name) visited acc = (visited', acc') →
          motive2 calledGlobalNames constantNames rank
            (filteredDeps calledGlobalNames constantNames name)
            (visiting.insert name) visited acc →
          motive1 calledGlobalNames constantNames rank name visiting visited acc := by
  intro name visiting visited acc hcn hvv visited' acc' heq ih2 hInv hRankVisiting hWP
  simp only [filteredDeps] at heq ih2
  have hboundDeps1 : ∀ d ∈ filteredDeps calledGlobalNames constantNames name, constantNames.contains d = true := by
    intro d hd
    simp only [filteredDeps, List.mem_filter] at hd
    exact hd.2
  have hboundDeps2 : ∀ d ∈ filteredDeps calledGlobalNames constantNames name, rank d < rank name := by
    intro d hd
    simp only [filteredDeps, List.mem_filter, Std.HashSet.mem_toList] at hd
    exact hRankEdge name d hcn hd.2 hd.1
  have hboundVisiting : ∀ n, (visiting.insert name).contains n = true → rank name ≤ rank n := by
    intro n hn
    rw [Std.HashSet.contains_insert] at hn
    rcases Bool.or_eq_true_iff.mp hn with h | h
    · have heqn : name = n := beq_iff_eq.mp h
      rw [heqn]; omega
    · exact hRankVisiting n h
  simp only [filteredDeps] at hboundDeps1 hboundDeps2
  obtain ⟨hAcc', hPre, hVis, hWP', hCover⟩ := ih2 (rank name) hboundDeps1 hboundDeps2 hboundVisiting hInv hWP
  rw [heq] at hAcc' hPre hVis hWP' hCover
  have hresult : visitConstantForTopoSort calledGlobalNames constantNames name visiting visited acc
      = (visited'.insert name, acc' ++ [name]) := by
    rw [visitConstantForTopoSort.eq_1, dif_pos hcn, dif_neg hvv]
    simp only [heq]
  rw [hresult]
  simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hvv
  have hNameNotVisited : visited.contains name = false := hvv.1
  have hNameNotVisiting : visiting.contains name = false := hvv.2
  have hNameInsertContains : (visiting.insert name).contains name = true := by
    simp [Std.HashSet.contains_insert]
  have hVisitedPrimeName : visited'.contains name = visited.contains name := hVis name hNameInsertContains
  have hNameNotInAccPrime : name ∉ acc' := by
    rw [← hAcc'.1 name, hVisitedPrimeName, hNameNotVisited]
    simp
  have hMemDep : ∀ dep ∈ filteredDeps calledGlobalNames constantNames name, dep ∈ acc' := by
    intro dep hdep
    have := hCover dep hdep
    exact (hAcc'.1 dep).mp this
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro x
    show (visited'.insert name).contains x ↔ x ∈ acc' ++ [name]
    simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, List.mem_append,
      List.mem_singleton, ← hAcc'.1 x]
    constructor
    · rintro (h | h)
      · exact Or.inr h.symm
      · exact Or.inl h
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl h.symm
  · show (acc' ++ [name]).Nodup
    rw [List.nodup_append]
    refine ⟨hAcc'.2, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact fun heq2 => hNameNotInAccPrime (heq2 ▸ ha)
  · show acc <+: acc' ++ [name]
    exact hPre.trans (List.prefix_append _ _)
  · intro y hy
    show (visited'.insert name).contains y = visited.contains y
    rcases Classical.em (y = name) with h | h
    · subst h
      exact absurd hy (by simp [hNameNotVisiting])
    · have hyIns : (visiting.insert name).contains y = true := by
        simp [Std.HashSet.contains_insert, hy]
      have hstep := hVis y hyIns
      rw [Std.HashSet.contains_insert, beq_eq_false_iff_ne.mpr (Ne.symm h), hstep]
      simp
  · intro d hd
    show WellPlaced calledGlobalNames constantNames (acc' ++ [name]) d
    rw [Std.HashSet.contains_insert] at hd
    rcases Bool.or_eq_true_iff.mp hd with h | h
    · have heqd : name = d := beq_iff_eq.mp h
      subst heqd
      refine ⟨by simp, acc', List.prefix_append _ _, hNameNotInAccPrime, hMemDep⟩
    · exact WellPlaced_mono calledGlobalNames constantNames acc' (acc' ++ [name]) (List.prefix_append _ _) d (hWP' d h)
  · intro _hcn2 _hvv2
    show (visited'.insert name).contains name = true
    simp [Std.HashSet.contains_insert]

private theorem topoCase3 : ∀ (name : String) (visiting visited : Std.HashSet String) (acc : List String),
    ¬ constantNames.contains name = true →
      motive1 calledGlobalNames constantNames rank name visiting visited acc := by
  intro name visiting visited acc hcn hInv _hRV hWP
  rw [visitConstantForTopoSort.eq_1]
  simp only [hcn]
  exact ⟨hInv, List.prefix_refl acc, fun _ _ => rfl, hWP, fun hc _ => absurd hc (by decide)⟩

private theorem topoCase4 : ∀ (visiting visited : Std.HashSet String) (acc : List String),
    motive2 calledGlobalNames constantNames rank [] visiting visited acc := by
  intro visiting visited acc boundRank _hcn _hrk _hvis hInv hWP
  rw [visitConstantsForTopoSort.eq_1]
  exact ⟨hInv, List.prefix_refl acc, fun _ _ => rfl, hWP, fun _ h => absurd h List.not_mem_nil⟩

private theorem topoCase5 : ∀ (visiting visited : Std.HashSet String) (acc : List String) (n : String)
    (rest : List String) (visited' : Std.HashSet String) (acc' : List String),
      visitConstantForTopoSort calledGlobalNames constantNames n visiting visited acc = (visited', acc') →
        motive1 calledGlobalNames constantNames rank n visiting visited acc →
          motive2 calledGlobalNames constantNames rank rest visiting visited' acc' →
            motive2 calledGlobalNames constantNames rank (n :: rest) visiting visited acc := by
  intro visiting visited acc n rest visited' acc' heq1 ih1 ih2 boundRank hcnAll hrankAll hvisAll hInv hWP
  have hcnN : constantNames.contains n = true := hcnAll n (List.mem_cons_self)
  have hcnRest : ∀ d ∈ rest, constantNames.contains d = true := fun d hd => hcnAll d (List.mem_cons_of_mem n hd)
  have hrankN : rank n < boundRank := hrankAll n (List.mem_cons_self)
  have hrankRest : ∀ d ∈ rest, rank d < boundRank := fun d hd => hrankAll d (List.mem_cons_of_mem n hd)
  have hvisitingNFalse : visiting.contains n = false := by
    cases hv : visiting.contains n with
    | false => rfl
    | true => exfalso; have := hvisAll n hv; omega
  have hRankVisitingN : ∀ m, visiting.contains m = true → rank n ≤ rank m := by
    intro m hm
    have := hvisAll m hm
    omega
  obtain ⟨hAcc1, hPre1, hVis1, hWP1', hMemN⟩ := ih1 hInv hRankVisitingN hWP
  rw [heq1] at hAcc1 hPre1 hVis1 hWP1' hMemN
  have hresult : visitConstantsForTopoSort calledGlobalNames constantNames (n :: rest) visiting visited acc
      = visitConstantsForTopoSort calledGlobalNames constantNames rest visiting visited' acc' := by
    rw [visitConstantsForTopoSort.eq_2, heq1]
  rw [hresult]
  obtain ⟨hAcc2, hPre2, hVis2, hWP2', hMemRest⟩ := ih2 boundRank hcnRest hrankRest hvisAll hAcc1 hWP1'
  have hnVisited' : visited'.contains n = true := hMemN hcnN hvisitingNFalse
  refine ⟨hAcc2, hPre1.trans hPre2, ?_, hWP2', ?_⟩
  · intro y hy
    rw [hVis2 y hy, hVis1 y hy]
  · intro dep hdep
    rcases List.mem_cons.mp hdep with h | h
    · subst h
      exact (hAcc2.1 dep).mpr (hPre2.mem ((hAcc1.1 dep).mp hnVisited'))
    · exact hMemRest dep h

include hRankEdge in
/-- The main correctness invariant for `visitConstantsForTopoSort`, established by structural
induction over its own well-founded recursion (`.induct`, generated automatically alongside it and
`visitConstantForTopoSort`). See `motive2`'s docstring for what the invariant actually says. -/
private theorem visitConstantsForTopoSort_correct : ∀ (deps : List String) (visiting visited : Std.HashSet String)
    (acc : List String), motive2 calledGlobalNames constantNames rank deps visiting visited acc :=
  visitConstantsForTopoSort.induct calledGlobalNames constantNames
    (motive1 calledGlobalNames constantNames rank) (motive2 calledGlobalNames constantNames rank)
    (topoCase1 calledGlobalNames constantNames rank) (topoCase2 calledGlobalNames constantNames rank hRankEdge)
    (topoCase3 calledGlobalNames constantNames rank) (topoCase4 calledGlobalNames constantNames rank)
    (topoCase5 calledGlobalNames constantNames rank)

end

/-- `sortConstantsTopologically`'s own fold over `constants` (nullary `visitConstantForTopoSort`
calls, one per constant, each restarting `visiting` at `∅`) is exactly `visitConstantsForTopoSort`
applied once to the whole name list -- the correctness proof reduces to a single call this way so
`visitConstantsForTopoSort_correct` applies directly to the top-level computation. -/
private theorem fold_eq_visitConstantsForTopoSort (calledGlobalNames : Std.HashMap String (Std.HashSet String))
    (constantNames : Std.HashSet String) (constants : List (String × SExpr))
    (visited : Std.HashSet String) (acc : List String) :
    constants.foldl
      (fun (visited, acc) (name, _) =>
        visitConstantForTopoSort calledGlobalNames constantNames name Std.HashSet.emptyWithCapacity visited acc)
      (visited, acc)
    = visitConstantsForTopoSort calledGlobalNames constantNames (constants.map Prod.fst)
        Std.HashSet.emptyWithCapacity visited acc := by
  induction constants generalizing visited acc with
  | nil => simp [visitConstantsForTopoSort.eq_1]
  | cons hd tl ih =>
    obtain ⟨name, sexpr⟩ := hd
    simp only [List.foldl_cons, List.map_cons]
    rw [visitConstantsForTopoSort.eq_2]
    obtain ⟨visited', acc'⟩ :=
      visitConstantForTopoSort calledGlobalNames constantNames name Std.HashSet.emptyWithCapacity visited acc
    simp only []
    rw [← ih]

private theorem contains_fold_insert (constants : List (String × SExpr)) (s0 : Std.HashSet String) (x : String) :
    (constants.foldl (fun s (name, _) => s.insert name) s0).contains x
      = (s0.contains x || (constants.map Prod.fst).contains x) := by
  induction constants generalizing s0 with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨name, sexpr⟩ := hd
    simp only [List.foldl_cons, List.map_cons, List.contains_cons]
    rw [ih, Std.HashSet.contains_insert, Bool.beq_comm]
    cases (x == name) <;> cases s0.contains x <;> cases (List.map Prod.fst tl).contains x <;> rfl

private theorem contains_fold_insertMap (constants : List (String × SExpr)) (s0 : Std.HashMap String SExpr)
    (x : String) : (constants.foldl (fun m (name, sexpr) => m.insert name sexpr) s0).contains x
      = (s0.contains x || (constants.map Prod.fst).contains x) := by
  induction constants generalizing s0 with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨name, sexpr⟩ := hd
    simp only [List.foldl_cons, List.map_cons, List.contains_cons]
    rw [ih, Std.HashMap.contains_insert, Bool.beq_comm]
    cases (x == name) <;> cases s0.contains x <;> cases (List.map Prod.fst tl).contains x <;> rfl

private theorem mem_fold_insertMap (constants : List (String × SExpr)) (x : String)
    (hx : x ∈ constants.map Prod.fst) :
    ∃ v, (constants.foldl (fun m (name, sexpr) => m.insert name sexpr) Std.HashMap.emptyWithCapacity)[x]? = some v := by
  have hc : (constants.foldl (fun m (name, sexpr) => m.insert name sexpr) Std.HashMap.emptyWithCapacity).contains x
      = true := by
    rw [contains_fold_insertMap]
    simp [hx]
  rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
  exact Option.isSome_iff_exists.mp hc

/-- If `pre` is a prefix of `l` containing a `p`-match but none of `q`, then `q` (scanned over all
of `l`) can't reach its match before `p` does: this is the "before" witness in `WellPlaced` turned
into an actual index comparison. -/
private theorem findIdx_prefix_lt {α : Type} (l pre : List α) (p q : α → Bool) (hpre : pre <+: l)
    (hq : ∀ x ∈ pre, q x = false) (hp : ∃ b ∈ pre, p b = true) :
    l.findIdx q > l.findIdx p := by
  obtain ⟨suffix, hsuf⟩ := hpre
  subst hsuf
  have hp' : pre.findIdx p < pre.length := List.findIdx_lt_length_of_exists hp
  have heqp : (pre ++ suffix).findIdx p = pre.findIdx p := by
    rw [List.findIdx_append, if_pos hp']
  have hnotEq : pre.findIdx q = pre.length := by
    rw [List.findIdx_eq_length]
    exact hq
  have heqq : (pre ++ suffix).findIdx q = suffix.findIdx q + pre.length := by
    rw [List.findIdx_append, if_neg (by omega)]
  omega

private theorem le_foldr_max (l : List Nat) (x : Nat) (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons hd tl ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with h | h
    · subst h; omega
    · have := ih h; omega

private theorem mem_filterMap_fst {α β γ : Type} [BEq α] (l : List α) (m : α → Option β) (f : α → β → γ)
    (y : γ) (hy : y ∈ l.filterMap (fun name => (m name).map (f name))) :
    ∃ a ∈ l, ∃ b, m a = some b ∧ f a b = y := by
  rw [List.mem_filterMap] at hy
  obtain ⟨a, ha, hf⟩ := hy
  cases h : m a with
  | none => rw [h] at hf; simp at hf
  | some b =>
    rw [h] at hf
    simp only [Option.map_some, Option.some.injEq] at hf
    exact ⟨a, ha, b, h, hf⟩

/-- `hAcyclic` captures the one fact about `calledGlobalNames` that real Lean elaboration
guarantees but its type alone doesn't: a `def`'s value can only reference declarations that already
exist, so declaration order is always a valid ranking function consistent with every dependency
edge. Without some such hypothesis the statement is false -- a direct 2-cycle (`A` calling `B` and
`B` calling `A`, both legal as far as the *types* here are concerned) would force
`sortedList` to place `A` both before and after `B`. -/
private theorem sortConstantsTopologically.isCorrect
  (postTranslationState : SExprState)
  (constants : List (String × SExpr))
  (sortedList : List (String × SExpr))
  (hSortedListIsResult : sortConstantsTopologically postTranslationState constants = sortedList)
  (hAcyclic : ∃ rank : String → Nat, ∀ a b, a ∈ constants.map Prod.fst → b ∈ constants.map Prod.fst →
    b ∈ postTranslationState.calledGlobalNames.getD a Std.HashSet.emptyWithCapacity → rank b < rank a) :
∀ constantName, constantName ∈ constants.map Prod.fst →
  ∀ dependsOn, dependsOn ∈ constants.map Prod.fst → dependsOn ≠ constantName →
    dependsOn ∈ postTranslationState.calledGlobalNames.getD constantName Std.HashSet.emptyWithCapacity →
      indexOfConstant constantName sortedList > indexOfConstant dependsOn sortedList := by
  obtain ⟨rank, hRankEdge0⟩ := hAcyclic
  intro constantName hCN dependsOn hDN hNe hDep
  let constantNames := constants.foldl (fun s (name, _) => s.insert name) Std.HashSet.emptyWithCapacity
  have hCNdef : constantNames = constants.foldl (fun s (name, _) => s.insert name) Std.HashSet.emptyWithCapacity := rfl
  have hContainsIff : ∀ x, constantNames.contains x = true ↔ x ∈ constants.map Prod.fst := by
    intro x
    rw [hCNdef, contains_fold_insert]
    simp
  have hRankEdge : ∀ a b, constantNames.contains a = true → constantNames.contains b = true →
      b ∈ postTranslationState.calledGlobalNames.getD a Std.HashSet.emptyWithCapacity → rank b < rank a := by
    intro a b ha hb hab
    exact hRankEdge0 a b ((hContainsIff a).mp ha) ((hContainsIff b).mp hb) hab
  have hInv0 : AccInv (Std.HashSet.emptyWithCapacity : Std.HashSet String) ([] : List String) :=
    ⟨fun x => by simp, by simp⟩
  have hWP0 : ∀ d, (Std.HashSet.emptyWithCapacity : Std.HashSet String).contains d = true →
      WellPlaced postTranslationState.calledGlobalNames constantNames [] d := by
    intro d hd; simp at hd
  let allNames := constants.map Prod.fst
  let boundRank := (allNames.map rank).foldr max 0 + 1
  have hcnAll : ∀ d ∈ allNames, constantNames.contains d = true := fun d hd => (hContainsIff d).mpr hd
  have hrankAll : ∀ d ∈ allNames, rank d < boundRank := by
    intro d hd
    have := le_foldr_max (allNames.map rank) (rank d) (List.mem_map_of_mem hd)
    omega
  have hvisAll : ∀ n, (Std.HashSet.emptyWithCapacity : Std.HashSet String).contains n = true → boundRank ≤ rank n := by
    intro n hn; simp at hn
  obtain ⟨_, _, _, hWPFinal, hCoverFinal⟩ :=
    visitConstantsForTopoSort_correct postTranslationState.calledGlobalNames constantNames rank hRankEdge allNames
      Std.HashSet.emptyWithCapacity Std.HashSet.emptyWithCapacity [] boundRank hcnAll hrankAll hvisAll hInv0 hWP0
  have hCNvisited : (visitConstantsForTopoSort postTranslationState.calledGlobalNames constantNames allNames
      Std.HashSet.emptyWithCapacity Std.HashSet.emptyWithCapacity []).1.contains constantName = true :=
    hCoverFinal constantName hCN
  obtain ⟨_, pre, hpreLe, hCNnotpre, hpredeps⟩ := hWPFinal constantName hCNvisited
  have hDepFiltered : dependsOn ∈ filteredDeps postTranslationState.calledGlobalNames constantNames constantName := by
    simp only [filteredDeps, List.mem_filter, Std.HashSet.mem_toList]
    exact ⟨hDep, (hContainsIff dependsOn).mpr hDN⟩
  have hDependsOnInPre : dependsOn ∈ pre := hpredeps dependsOn hDepFiltered
  have hSortedEq : sortedList = (visitConstantsForTopoSort postTranslationState.calledGlobalNames constantNames
      allNames Std.HashSet.emptyWithCapacity Std.HashSet.emptyWithCapacity []).2.filterMap
      (fun name => ((constants.foldl (fun m (name, sexpr) => m.insert name sexpr)
        Std.HashMap.emptyWithCapacity)[name]?).map (name, ·)) := by
    rw [← hSortedListIsResult]
    simp only [sortConstantsTopologically, fold_eq_visitConstantsForTopoSort]
    rfl
  obtain ⟨valDep, hvalDepEq⟩ := mem_fold_insertMap constants dependsOn hDN
  have hDepPairMem : (dependsOn, valDep) ∈ pre.filterMap
      (fun name => ((constants.foldl (fun m (name, sexpr) => m.insert name sexpr)
        Std.HashMap.emptyWithCapacity)[name]?).map (name, ·)) := by
    rw [List.mem_filterMap]
    exact ⟨dependsOn, hDependsOnInPre, by simp [hvalDepEq]⟩
  have hPreFilterPrefix : pre.filterMap
      (fun name => ((constants.foldl (fun m (name, sexpr) => m.insert name sexpr)
        Std.HashMap.emptyWithCapacity)[name]?).map (name, ·)) <+: sortedList := by
    rw [hSortedEq]
    obtain ⟨suf, hsuf⟩ := hpreLe
    rw [← hsuf, List.filterMap_append]
    exact List.prefix_append _ _
  have hNotConstantName : ∀ y ∈ pre.filterMap
      (fun name => ((constants.foldl (fun m (name, sexpr) => m.insert name sexpr)
        Std.HashMap.emptyWithCapacity)[name]?).map (name, ·)), (y.1 == constantName) = false := by
    intro y hy
    obtain ⟨a, ha, b, hab, hfab⟩ := mem_filterMap_fst pre _ (fun name => (name, ·)) y hy
    have : y.1 = a := by rw [← hfab]
    rw [this]
    apply beq_eq_false_iff_ne.mpr
    intro heq
    exact hCNnotpre (heq ▸ ha)
  exact findIdx_prefix_lt sortedList
    (pre.filterMap (fun name => ((constants.foldl (fun m (name, sexpr) => m.insert name sexpr)
      Std.HashMap.emptyWithCapacity)[name]?).map (name, ·)))
    (·.1 == dependsOn) (·.1 == constantName)
    hPreFilterPrefix hNotConstantName ⟨(dependsOn, valDep), hDepPairMem, by simp⟩
