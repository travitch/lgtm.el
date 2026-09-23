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
      let repoName := (System.FilePath.mk repoPath).fileName.getD "No Name"
      let r := Repository.mk repoName repoPath ⟨baseRevision.1⟩ (info.repoCommits.map (λ (rev, msg) => (GitRevision.mk rev, msg))).toList
      repositories := r :: repositories


  if commitsWithoutRepository.isEmpty && repositoriesWithoutCommits.isEmpty then
    pure (repositories.mergeSort (λ a b => a.name < b.name))
  else
    throw ⟨commitsWithoutRepository, repositoriesWithoutCommits⟩

/- def assignCommitsToRepositories (repositoryPaths : List String) (commits : List String) : List Repository := sorry -/
