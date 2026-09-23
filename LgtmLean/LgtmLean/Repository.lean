module

import Std

public import LgtmLean.Basic

public structure RepositoryErrors where
  commitsWithoutRepository : List String
  repositoriesWithoutCommits : List String

public structure PerRepositoryInfo (commitsInChange : List String) where
  referencedCommits : List Nat
  repoCommits : Array (String × String)
  /-- Every referenced commit is followed by an older commit in this history.

  That older commit is the base revision the changeset is applied against, so a
  commit may only be referenced if the history actually extends past it. -/
  referencedCommitsHaveBase : ∀ idx ∈ referencedCommits, idx + 1 < repoCommits.size
  /-- Every commit of the changeset that this history contains has a base revision.

  This is the per-repository instance of the caller's precondition; it is what
  licenses `addCommitRef` on a commit found in this history. -/
  changeCommitsHaveBase : ∀ commit ∈ commitsInChange, ∀ idx,
    (repoCommits.map (λ c => c.1)).idxOf? commit = some idx → idx + 1 < repoCommits.size

public def addCommitRef {commitsInChange : List String} (idx : Nat)
    (info : PerRepositoryInfo commitsInChange)
    (hIdx : idx + 1 < info.repoCommits.size) : PerRepositoryInfo commitsInChange where
  referencedCommits := idx :: info.referencedCommits
  repoCommits := info.repoCommits
  referencedCommitsHaveBase := by
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact hIdx
    · exact info.referencedCommitsHaveBase i hi
  changeCommitsHaveBase := info.changeCommitsHaveBase

/-- Record a reference to `commit` in the first repository of `perRepositoryInfo` whose history
contains it, returning that repository's path along with its updated info.

Finding the commit and recording it are fused on purpose: the index is only ever consumed against
the very `PerRepositoryInfo` it was found in, so `changeCommitsHaveBase` discharges
`addCommitRef`'s bound right where the index is produced.  Returning a bare index instead would
force the caller to search the owning repository's history a second time, since a bound taken from
any other copy of that history says nothing about `info.repoCommits`. -/
public def assignCommitsToRepositoryHistories.findCommitRepoIndex {commitsInChange : List String}
    (commit : String) (hCommit : commit ∈ commitsInChange)
    (perRepositoryInfo : Std.HashMap String (PerRepositoryInfo commitsInChange)) :
    Option (String × PerRepositoryInfo commitsInChange) := do
  for (repoPath, info) in perRepositoryInfo.toList do
    match hFound : (info.repoCommits.map (λ c => c.1)).idxOf? commit with
    | none => pure ()
    | some idx =>
      return (repoPath, addCommitRef idx info (info.changeCommitsHaveBase commit hCommit idx hFound))

  none

/-- What a successful `findCommitRepoIndex` tells the caller about the map it searched.

The returned path is a genuine key of `perRepositoryInfo`, the returned info keeps that entry's
history verbatim, and it has at least one referenced commit — which is what later makes the
repository survive into the result list. -/
private theorem assignCommitsToRepositoryHistories.findCommitRepoIndex_spec
    {commitsInChange : List String} (commit : String) (hCommit : commit ∈ commitsInChange)
    (perRepositoryInfo : Std.HashMap String (PerRepositoryInfo commitsInChange))
    {repoPath : String} {updated : PerRepositoryInfo commitsInChange}
    (hFind : assignCommitsToRepositoryHistories.findCommitRepoIndex commit hCommit perRepositoryInfo
      = some (repoPath, updated)) :
    ∃ info, perRepositoryInfo[repoPath]? = some info ∧ updated.repoCommits = info.repoCommits ∧
      updated.referencedCommits ≠ [] ∧ commit ∈ info.repoCommits.map (λ c => c.1) := by
  suffices h : ∃ info, (repoPath, info) ∈ perRepositoryInfo.toList ∧
      updated.repoCommits = info.repoCommits ∧ updated.referencedCommits ≠ [] ∧
      commit ∈ info.repoCommits.map (λ c => c.1) by
    obtain ⟨info, hMem, hRest⟩ := h
    exact ⟨info, Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hMem, hRest⟩
  unfold assignCommitsToRepositoryHistories.findCommitRepoIndex at hFind
  generalize perRepositoryInfo.toList = l at hFind
  induction l with
  | nil => simp at hFind
  | cons hd tl ih =>
    obtain ⟨p, info⟩ := hd
    rw [List.forIn_cons] at hFind
    simp only at hFind
    split at hFind
    · simp only [pure_bind] at hFind
      obtain ⟨info', hMem, hRest⟩ := ih hFind
      exact ⟨info', List.mem_cons_of_mem _ hMem, hRest⟩
    · rename_i idx hFound
      simp only [pure_bind] at hFind
      obtain ⟨rfl, rfl⟩ := hFind
      exact ⟨info, List.mem_cons_self .., rfl, List.cons_ne_nil _ _,
        Array.isSome_idxOf?.mp (by rw [hFound]; rfl)⟩

/-- Some repository in `perRepositoryInfo` has `commit` in its history and is already referenced
by the changeset.

This is the invariant carried through the commit-assignment loop.  Being referenced is what makes
a repository survive into the result list, and its history is where the result's commits are read
from, so the two halves together are exactly what the final goal needs. -/
private def assignCommitsToRepositoryHistories.CommitCovered {commitsInChange : List String}
    (perRepositoryInfo : Std.HashMap String (PerRepositoryInfo commitsInChange))
    (commit : String) : Prop :=
  ∃ (repoPath : String) (info : PerRepositoryInfo commitsInChange),
    perRepositoryInfo[repoPath]? = some info ∧
      commit ∈ info.repoCommits.map (λ c => c.1) ∧ info.referencedCommits ≠ []

/-- Recording a commit against the repository `findCommitRepoIndex` picked keeps every already
covered commit covered.

The info being inserted reuses the history stored at `repoPath` and only extends its referenced
commits, so no existing witness is invalidated — not even one pointing at `repoPath` itself. -/
private theorem assignCommitsToRepositoryHistories.CommitCovered.insert
    {commitsInChange : List String} {commit : String} (hCommit : commit ∈ commitsInChange)
    {perRepositoryInfo : Std.HashMap String (PerRepositoryInfo commitsInChange)}
    {repoPath : String} {updated : PerRepositoryInfo commitsInChange}
    (hFind : assignCommitsToRepositoryHistories.findCommitRepoIndex commit hCommit perRepositoryInfo
      = some (repoPath, updated))
    {c : String} (hc : CommitCovered perRepositoryInfo c) :
    CommitCovered (perRepositoryInfo.insert repoPath updated) c := by
  obtain ⟨p, info₀, hGet, hMem, hRefs⟩ := hc
  obtain ⟨info, hGetR, hRepoCommits, hRefs', _⟩ :=
    assignCommitsToRepositoryHistories.findCommitRepoIndex_spec commit hCommit perRepositoryInfo hFind
  by_cases hEq : repoPath = p
  · subst hEq
    rw [hGetR, Option.some.injEq] at hGet
    subst hGet
    exact ⟨repoPath, updated, Std.HashMap.getElem?_insert_self, by rw [hRepoCommits]; exact hMem,
      hRefs'⟩
  · refine ⟨p, info₀, ?_, hMem, hRefs⟩
    rw [Std.HashMap.getElem?_insert, if_neg (by simpa using hEq)]
    exact hGet

/-- Everything the commit-assignment loop guarantees about its final state.

Coverage established before the loop survives it, the missing list only grows, and every commit
the loop visits ends up either recorded as missing or covered.  On the success path the missing
list is empty, so the last clause collapses to coverage. -/
private theorem assignCommitsToRepositoryHistories.assignLoop_spec
    {commitsInChange : List String} (l : List { c // c ∈ commitsInChange })
    (perRepositoryInfo : Std.HashMap String (PerRepositoryInfo commitsInChange))
    (missing : List String)
    {s : Std.HashMap String (PerRepositoryInfo commitsInChange) × List String}
    (hLoop : (forIn l (perRepositoryInfo, missing) (λ entry __s =>
        match assignCommitsToRepositoryHistories.findCommitRepoIndex entry.val entry.property __s.fst with
        | none => pure (ForInStep.yield (__s.fst, entry.val :: __s.snd))
        | some (repoPath, updatedInfo) =>
          pure (ForInStep.yield (__s.fst.insert repoPath updatedInfo, __s.snd))) :
      Except RepositoryErrors _) = Except.ok s) :
    (∀ c, CommitCovered perRepositoryInfo c → CommitCovered s.fst c) ∧
      (∀ x ∈ missing, x ∈ s.snd) ∧
      (∀ e ∈ l, e.val ∈ s.snd ∨ CommitCovered s.fst e.val) := by
  induction l generalizing perRepositoryInfo missing with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at hLoop
    subst hLoop
    exact ⟨fun _ h => h, fun _ h => h, by simp⟩
  | cons e tl ih =>
    rw [List.forIn_cons] at hLoop
    simp only at hLoop
    split at hLoop
    · simp only [pure_bind] at hLoop
      obtain ⟨hMono, hMissing, hAll⟩ := ih perRepositoryInfo (e.val :: missing) hLoop
      refine ⟨hMono, fun x hx => hMissing x (List.mem_cons_of_mem _ hx), ?_⟩
      intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · exact Or.inl (hMissing _ (List.mem_cons_self ..))
      · exact hAll e' he'
    · rename_i _ repoPath updated hFind
      simp only [pure_bind] at hLoop
      obtain ⟨hMono, hMissing, hAll⟩ := ih (perRepositoryInfo.insert repoPath updated) missing hLoop
      refine ⟨fun c hc => hMono c (CommitCovered.insert e.property hFind hc), hMissing, ?_⟩
      intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · refine Or.inr (hMono _ ?_)
        obtain ⟨info, _, hRepoCommits, hRefs, hMem⟩ :=
          findCommitRepoIndex_spec e'.val e'.property perRepositoryInfo hFind
        exact ⟨repoPath, updated, Std.HashMap.getElem?_insert_self,
          by rw [hRepoCommits]; exact hMem, hRefs⟩
      · exact hAll e' he'

public def BaseRevisionExists (historyIndex : List (String × Array (String × String))) (commitsInChange : List String) : Prop :=
  ∀ entry ∈ historyIndex, ∀ commit ∈ commitsInChange, ∀ idx,
        (entry.2.map (λ c => c.1)).idxOf? commit = some idx →
          idx + 1 < entry.2.size

public def assignCommitsToRepositoryHistories (historyIndex : List (String × Array (String × String))) (commitsInChange : List String)
    (hBaseRevisionExists : BaseRevisionExists historyIndex commitsInChange) : Except RepositoryErrors (List Repository) := do
  let mut perRepositoryInfo : Std.HashMap String (PerRepositoryInfo commitsInChange) := Std.HashMap.emptyWithCapacity

  let mut commitsWithoutRepository := []
  let mut repositoriesWithoutCommits := []

  for entry in historyIndex.attach do
    perRepositoryInfo := perRepositoryInfo.insert entry.val.1
      ⟨[], entry.val.2, by simp, hBaseRevisionExists entry.val entry.property⟩

  for entry in commitsInChange.attach do
    let commit := entry.val
    match assignCommitsToRepositoryHistories.findCommitRepoIndex commit entry.property perRepositoryInfo with
    | none => do
      commitsWithoutRepository := commit :: commitsWithoutRepository
    | some (repoPath, updatedInfo) => do
      perRepositoryInfo := perRepositoryInfo.insert repoPath updatedInfo

  perRepositoryInfo := perRepositoryInfo.map (λ _repoPath info =>
    { referencedCommits := info.referencedCommits.mergeSort
      repoCommits := info.repoCommits
      referencedCommitsHaveBase := by
        intro idx hIdx
        exact info.referencedCommitsHaveBase idx (List.mem_mergeSort.mp hIdx)
      changeCommitsHaveBase := info.changeCommitsHaveBase })

  let mut repositories := []

  for (repoPath, info) in perRepositoryInfo.toList do
    match hRefs : info.referencedCommits with
    | [] => do
      repositoriesWithoutCommits := repoPath :: repositoriesWithoutCommits
    | rc :: rcs => do
      let lastIdx := (rc :: rcs).getLast (List.cons_ne_nil rc rcs)
      let baseRevision := info.repoCommits[lastIdx + 1]'(by
        refine info.referencedCommitsHaveBase lastIdx ?_
        rw [hRefs]
        exact List.getLast_mem _)
      let repoName := (System.FilePath.mk repoPath).fileName.getD repoPath
      let r := Repository.mk repoName repoPath ⟨baseRevision.1⟩ (info.repoCommits.map (λ (rev, msg) => (GitRevision.mk rev, msg))).toList
      repositories := r :: repositories


  if commitsWithoutRepository.isEmpty && repositoriesWithoutCommits.isEmpty then
    pure (repositories.mergeSort (λ a b => a.name < b.name))
  else
    throw ⟨commitsWithoutRepository, repositoriesWithoutCommits⟩

/-- Split a successful `Except` bind into its two successful halves.

`assignCommitsToRepositoryHistories` is a three-stage `do` block in `Except`; this names each
stage's result without having to unfold the loop bodies. -/
private theorem Except.bind_eq_ok {ε α β : Type _} {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = Except.ok b ↔ ∃ a, x = Except.ok a ∧ f a = Except.ok b := by
  cases x <;> simp [Bind.bind, Except.bind]

/-- Run a non-throwing `for` loop whose body accumulates monotonically.

`Good a` is an obligation discharged by a state; the body must preserve every obligation already
discharged and, for the element it is visiting, discharge that element's own obligation whenever
`Cond` holds of it.  The conclusion is that the final state discharges the obligation of every
element the loop visited.

Stating this generically avoids having to transcribe the loop body, whose `match` on
`referencedCommits` is dependent — the body stays an opaque `g` that unification recovers from the
loop hypothesis. -/
private theorem forIn_yield_accum {ε σ : Type u} {α : Type v}
    (l : List α) (init : σ) (g : α → σ → Except ε (ForInStep σ))
    (Good : α → σ → Prop) (Cond : α → Prop)
    (hStep : ∀ a st, ∃ st', g a st = pure (ForInStep.yield st') ∧
      (∀ a', Good a' st → Good a' st') ∧ (Cond a → Good a st'))
    {s : σ} (hLoop : forIn l init g = Except.ok s) :
    (∀ a, Good a init → Good a s) ∧ (∀ a ∈ l, Cond a → Good a s) := by
  induction l generalizing init with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at hLoop
    subst hLoop
    exact ⟨fun _ h => h, by simp⟩
  | cons a l ih =>
    obtain ⟨st', hg, hMono, hCond⟩ := hStep a init
    rw [List.forIn_cons, hg] at hLoop
    simp only [pure_bind] at hLoop
    obtain ⟨hMono', hAll⟩ := ih st' hLoop
    refine ⟨fun a' h => hMono' a' (hMono a' h), ?_⟩
    intro a' ha' hc
    rcases List.mem_cons.mp ha' with rfl | ha'
    · exact hMono' a' (hCond hc)
    · exact hAll a' ha' hc

private theorem assignCommitsToRepositoryHistories.allCommitsInResult
  (historyIndex : List (String × Array (String × String)))
  (commitsInChange : List String)
  (hBaseRevisionExists : BaseRevisionExists historyIndex commitsInChange)
  (result : List Repository)
  (hResult : assignCommitsToRepositoryHistories historyIndex commitsInChange hBaseRevisionExists = Except.ok result) :
  ∀ hash, hash ∈ commitsInChange → (∃ r, r ∈ result ∧ GitRevision.mk hash ∈ r.commits.map (λ c => c.1)) := by
  intro hash hHash
  unfold assignCommitsToRepositoryHistories at hResult
  simp only [Except.bind_eq_ok] at hResult
  obtain ⟨s₂, hs₂, s₃, hs₃, s₄, hs₄, hFinal⟩ := hResult
  split at hFinal
  · rename_i hCond
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hCond
    obtain ⟨hNoMissing, hNoEmptyRepos⟩ := hCond
    simp only [pure, Except.pure, Except.ok.injEq] at hFinal
    subst hFinal
    obtain ⟨_, _, hAssigned⟩ := assignLoop_spec commitsInChange.attach s₂ [] hs₃
    have hCovered : CommitCovered s₃.fst hash := by
      rcases hAssigned ⟨hash, hHash⟩ (List.mem_attach ..) with hMissing | hCov
      · rw [hNoMissing] at hMissing
        simp at hMissing
      · exact hCov
    obtain ⟨repoPath, info, hGet, hMem, hRefs⟩ := hCovered
    -- Loop 3 visits every entry of the post-processed map and, for each one that is referenced,
    -- pushes a repository carrying that entry's history.
    obtain ⟨-, hBuilt⟩ := forIn_yield_accum _ _ _
      (fun x st => ∃ r ∈ st.snd,
        r.commits = (x.snd.repoCommits.map (λ c => (GitRevision.mk c.1, c.2))).toList)
      (fun x => x.snd.referencedCommits ≠ []) (by
        intro a st
        split
        · rename_i hEmpty
          exact ⟨_, rfl, fun _ h => h, fun hCond => absurd hEmpty hCond⟩
        · exact ⟨_, rfl, fun _ h => h.imp (fun _ hr => ⟨List.mem_cons_of_mem _ hr.1, hr.2⟩),
            fun _ => ⟨_, List.mem_cons_self .., rfl⟩⟩) hs₄
    -- `repoPath`'s entry survives the `HashMap.map`, with its history intact and its referenced
    -- commits merely sorted.
    obtain ⟨r, hrMem, hrCommits⟩ := hBuilt _
      (Std.HashMap.toList_map.mem_iff.mpr
        (List.mem_map_of_mem (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hGet)))
      (by
        obtain ⟨idx, hIdx⟩ := List.exists_mem_of_ne_nil _ hRefs
        exact List.ne_nil_of_mem (List.mem_mergeSort.mpr hIdx))
    refine ⟨r, List.mem_mergeSort.mpr hrMem, ?_⟩
    rw [hrCommits]
    obtain ⟨c, hc, hcEq⟩ := Array.mem_map.mp hMem
    exact List.mem_map.mpr ⟨(GitRevision.mk c.1, c.2),
      Array.mem_toList_iff.mpr (Array.mem_map.mpr ⟨c, hc, rfl⟩), by rw [hcEq]⟩
  · simp at hFinal

/- def assignCommitsToRepositories (repositoryPaths : List String) (commits : List String) : List Repository := sorry -/
