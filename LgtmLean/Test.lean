import Std
import Extractor
import LgtmLean

/-! # End-to-end tests for the elisp extraction

`lake test` runs this executable. It checks three things:

1. **The pipeline ran to completion.** There are no `LExpr.opaque` placeholders, which would turn
   into errors in the generated elisp.  There are also no calls to functions that were not defined
   (or not builtins).

2. **The generated elisp is really elisp.** It is byte-compiled by `emacs -Q --batch`, which fails
   on a syntax error and warns about calls to functions that exist nowhere in the file.

3. **The translation preserved meaning.** `allChecks` is a list of concrete calls into the extracted
   code. Every expected value is obtained by running the Lean definition the elisp was extracted
   from, and both it and the call's arguments are rendered into elisp source by `ToElisp`. So a
   check compares the Lean function's answer against the extracted function's answer on the same
   input, and a translation that produces well-formed elisp with the wrong meaning fails here rather
   than silently in the UI. -/

/-! ## Rendering Lean values as elisp -/

/-- Render a value as Emacs Lisp *source text* that evaluates to the runtime representation the
extraction gives that value. See [ref:inductive-type-representation] in `Render.lean` for the
representation being mirrored here. -/
class ToElisp (α : Type) where
  toElisp : α → String

export ToElisp (toElisp)

/-- An elisp call form, e.g. `(make-lgtm-comment-ref "c1")`. -/
def elispCall (fn : String) (args : List String) : String :=
  "(" ++ String.intercalate " " (fn :: args) ++ ")"

/-- An elisp string literal. -/
def elispString (s : String) : String := "\"" ++ escapeLispString s ++ "\""

instance : ToElisp String := ⟨elispString⟩
instance : ToElisp Nat := ⟨toString⟩
instance : ToElisp Char := ⟨charToLispSyntax⟩
instance : ToElisp Bool := ⟨fun b => if b then "t" else "nil"⟩
instance : ToElisp Unit := ⟨fun _ => "'unit"⟩
instance : ToElisp System.FilePath := ⟨fun p => elispString p.toString⟩

/-- `none` is `nil` and `some x` is just `x`: the extraction represents `Option` by presence, which
is why `Option.isSome` translates to the value itself. -/
instance [ToElisp α] : ToElisp (Option α) where
  toElisp
    | none => "nil"
    | some a => toElisp a

instance [ToElisp α] : ToElisp (List α) where
  toElisp xs := if xs.isEmpty then "nil" else elispCall "list" (xs.map toElisp)

/-- Tuples are vectors, so `Prod.fst`/`Prod.snd` are `(elt p 0)`/`(elt p 1)`. -/
instance [ToElisp α] [ToElisp β] : ToElisp (α × β) where
  toElisp p := elispCall "vector" [toElisp p.1, toElisp p.2]

instance [ToElisp ε] [ToElisp α] : ToElisp (Except ε α) where
  toElisp
    | .ok v => elispCall "vector" ["'except-ok", toElisp v]
    | .error e => elispCall "vector" ["'except-error", toElisp e]

/-- Hash maps become `equal`-tested hash tables, built by the test harness'
`lgtm-test--hash-table` from the association list. Compares using `equal` because
Lean compares keys by value. -/
instance [BEq α] [Hashable α] [ToElisp α] [ToElisp β] : ToElisp (Std.HashMap α β) where
  toElisp m := elispCall "lgtm-test--hash-table" [toElisp m.toList]

/-! ### The `LgtmLean` types

Structures are `cl-defstruct` records, built positionally through the generated constructor;
nullary constructors are symbols; constructors with fields are vectors tagged with the constructor
symbol. -/

instance : ToElisp CommentRef := ⟨fun r => elispCall "make-lgtm-comment-ref" [toElisp r.id]⟩
instance : ToElisp ServerId := ⟨fun s => elispCall "make-lgtm--server-id" [toElisp s.id]⟩
instance : ToElisp GitRevision := ⟨fun r => elispCall "make-lgtm--git-revision" [toElisp r.hash]⟩
instance : ToElisp FileRef := ⟨fun r => elispCall "make-lgtm--file-ref" [toElisp r.path]⟩
instance : ToElisp ChangesetStatus := ⟨fun s => elispCall "make-lgtm--changeset-status" [toElisp s.status]⟩

instance : ToElisp FileVersion where
  toElisp
    | .base => "'file-version-base"
    | .current => "'file-version-current"

instance : ToElisp ModificationType where
  toElisp
    | .modified => "'modification-type-modified"
    | .added => "'modification-type-added"
    | .deleted => "'modification-type-deleted"
    | .renamed => "'modification-type-renamed"
    | .copied => "'modification-type-copied"
    | .typechange => "'modification-type-typechange"

instance : ToElisp ThreadLocation where
  toElisp
    | .topLevel => "'thread-location-top-level"
    | .lineNumber n => elispCall "vector" ["'thread-location-line-number", toElisp n]

instance : ToElisp RepositoryRef where
  toElisp r := elispCall "make-lgtm--repository-ref" [toElisp r.name, toElisp r.path, toElisp r.baseRevision]

instance : ToElisp ModifiedFileRef where
  toElisp r := elispCall "make-lgtm--modified-file-ref"
    [toElisp r.repositoryRef, toElisp r.modificationType, toElisp r.baseFileName,
     toElisp r.baseFileHash, toElisp r.currentFileName, toElisp r.currentFileHash]

instance : ToElisp CommentFileLocation where
  toElisp l := elispCall "make-lgtm-comment-file-location"
    [toElisp l.version, toElisp l.fileRef, toElisp l.startLine, toElisp l.startColumn,
     toElisp l.endLine, toElisp l.endColumn]

instance : ToElisp CommentLocation where
  toElisp
    | .topLevel => "'comment-location-top-level"
    | .fileLocation l => elispCall "vector" ["'comment-location-file-location", toElisp l]

instance : ToElisp Comment where
  toElisp c := elispCall "make-lgtm-comment"
    [toElisp c.ref, toElisp c.backendId, toElisp c.location, toElisp c.isPublished,
     toElisp c.author, toElisp c.createdTimestamp, toElisp c.updatedTimestamp, toElisp c.parent,
     toElisp c.replyToId, toElisp c.content]

instance [ToElisp α] : ToElisp (Tree α) where
  toElisp t := elispCall "make-lgtm--tree" [toElisp t.value, toElisp t.children]

instance : ToElisp CommentThreads where
  toElisp t := elispCall "make-lgtm--comment-threads"
    [toElisp t.commentTreeNodes, toElisp t.serverCommentIds, toElisp t.locationRoots]

instance : ToElisp SelectedComment where
  toElisp s := elispCall "make-lgtm--selected-comment" [toElisp s.version, toElisp s.thread, toElisp s.comment]

instance : ToElisp CommentManager where
  toElisp m := elispCall "make-lgtm--comment-manager"
    [toElisp m.comments, toElisp m.topLevelThreads, toElisp m.selectedComment]

instance : ToElisp CommentBootstrapState where
  toElisp b := elispCall "make-lgtm--comment-bootstrap-state"
    [toElisp b.topLevelComments, toElisp b.baseComments, toElisp b.currentComments]

instance : ToElisp CommentTreeBootstrapState where
  toElisp b := elispCall "make-lgtm--comment-tree-bootstrap-state"
    [toElisp b.commentTreeNodes, toElisp b.serverCommentIds, toElisp b.locationRoots]

instance : ToElisp ModifiedFileState where
  toElisp s := elispCall "make-lgtm--modified-file-state"
    [toElisp s.ref, toElisp s.fileRef, toElisp s.selectedComment, toElisp s.baseThreads,
     toElisp s.currentThreads]

instance : ToElisp ModifiedFileManager where
  toElisp m := elispCall "make-lgtm--modified-file-manager" [toElisp m.state, toElisp m.modifiedFiles]

/-! ## Checks -/

/-- One concrete comparison: evaluate `actual` (a call into the extracted elisp) in emacs and
compare it against `expected` (the elisp rendering of what the Lean function returned). -/
structure ElispCheck where
  /-- What is being checked; reported when it fails. -/
  name : String
  /-- The elisp expression under test. -/
  actual : String
  /-- The elisp source of the value Lean computed. -/
  expected : String

def check [ToElisp β] (name : String) (actual : String) (expected : β) : ElispCheck :=
  { name := name, actual := actual, expected := toElisp expected }

/-- A check on a `Bool`-valued function, compared by *truthiness* rather than by value.

The extraction deliberately answers some boolean questions with a truthy value that isn't `t` --
`Option.isSome` becomes the option itself, for instance -- so `(if .. t nil)` normalizes the answer
before comparing. Anything whose Lean type isn't `Bool` should use `check`, which compares exactly. -/
def checkBool (name : String) (actual : String) (expected : Bool) : ElispCheck :=
  check name s!"(if {actual} t nil)" expected

/-- A check that a fixture couldn't be built; always fails, so a `dite` that unexpectedly took its
`else` branch is reported rather than silently dropping the checks it guards. -/
def missingFixture (name : String) : ElispCheck :=
  { name := s!"fixture unavailable: {name}", actual := "nil", expected := "t" }

/-! The `checkN` helpers apply a Lean function and the elisp function it was extracted to, to the
same arguments so the two sides cannot drift apart. -/

def check1 [ToElisp α] [ToElisp β] (fn : String) (f : α → β) (a : α) : ElispCheck :=
  check fn (elispCall fn [toElisp a]) (f a)

def check2 [ToElisp α] [ToElisp β] [ToElisp γ] (fn : String) (f : α → β → γ) (a : α) (b : β) : ElispCheck :=
  check fn (elispCall fn [toElisp a, toElisp b]) (f a b)

def check3 [ToElisp α] [ToElisp β] [ToElisp γ] [ToElisp δ] (fn : String) (f : α → β → γ → δ)
    (a : α) (b : β) (c : γ) : ElispCheck :=
  check fn (elispCall fn [toElisp a, toElisp b, toElisp c]) (f a b c)

def check4 [ToElisp α] [ToElisp β] [ToElisp γ] [ToElisp δ] [ToElisp ε] (fn : String)
    (f : α → β → γ → δ → ε) (a : α) (b : β) (c : γ) (d : δ) : ElispCheck :=
  check fn (elispCall fn [toElisp a, toElisp b, toElisp c, toElisp d]) (f a b c d)

def checkBool1 [ToElisp α] (fn : String) (f : α → Bool) (a : α) : ElispCheck :=
  checkBool fn (elispCall fn [toElisp a]) (f a)

def checkBool2 [ToElisp α] [ToElisp β] (fn : String) (f : α → β → Bool) (a : α) (b : β) : ElispCheck :=
  checkBool fn (elispCall fn [toElisp a, toElisp b]) (f a b)

def checkBool3 [ToElisp α] [ToElisp β] [ToElisp γ] (fn : String) (f : α → β → γ → Bool)
    (a : α) (b : β) (c : γ) : ElispCheck :=
  checkBool fn (elispCall fn [toElisp a, toElisp b, toElisp c]) (f a b c)

/-- A check on a derived `DecidableEq` instance: the extracted decision procedure against Lean's
own answer. -/
def checkDecEq [ToElisp α] [DecidableEq α] (fn : String) (a b : α) : ElispCheck :=
  checkBool fn (elispCall fn [toElisp a, toElisp b]) (decide (a = b))

/-- A check that `name` was *not* emitted, because `pruneToReachable` found nothing calling it. -/
def checkPruned (name : String) : ElispCheck :=
  checkBool s!"pruned: {name}" s!"(or (fboundp '{name}) (boundp '{name}))" false

/-! ## Fixtures -/

namespace Fixtures

def repositoryRef : RepositoryRef := ⟨"lgtm", "/src/lgtm", ⟨"base-rev"⟩⟩

def modifiedFileRef : ModifiedFileRef :=
  ⟨repositoryRef, .modified, "src/main.c", ⟨"base-hash"⟩, "src/main.c", ⟨"current-hash"⟩⟩

def otherFileRef : ModifiedFileRef :=
  ⟨repositoryRef, .added, "src/new.c", ⟨"base-hash"⟩, "src/new.c", ⟨"current-hash"⟩⟩

def fileLoc (line : Nat) (version : FileVersion := .current) (ref : ModifiedFileRef := modifiedFileRef) :
    CommentLocation :=
  .fileLocation ⟨version, ref, line, 0, line, 10⟩

def mkComment (id serverId : String) (parent : Option String) (timestamp : Nat)
    (location : CommentLocation) (content : String) : Comment :=
  { ref := ⟨id⟩, backendId := some ⟨serverId⟩, location := location, isPublished := true,
    author := "alice", createdTimestamp := timestamp, updatedTimestamp := timestamp + 1,
    parent := parent.map ServerId.mk, replyToId := parent.map ServerId.mk, content := content }

/-- Two top-level threads, one of them with a reply. `c3` is deliberately older than `c1` so that
an ordering that ignores timestamps (or sorts the wrong way) is visible in the results, and `c2`'s
content exercises string escaping. -/
def topLevelComments : List Comment :=
  [ mkComment "c1" "s1" none 100 .topLevel "the first thread",
    mkComment "c2" "s2" (some "s1") 200 .topLevel "a reply that \"quotes\" and \\ escapes",
    mkComment "c3" "s3" none 50 .topLevel "an older thread" ]

/-- A batch spanning both file versions and both files, for the grouping functions. -/
def mixedComments : List Comment :=
  topLevelComments ++
  [ mkComment "b1" "sb1" none 10 (fileLoc 12 .base) "on the base version",
    mkComment "b2" "sb2" (some "sb1") 20 (fileLoc 12 .base) "reply on the base version",
    mkComment "f1" "sf1" none 30 (fileLoc 7) "on the current version",
    mkComment "f2" "sf2" none 40 (fileLoc 99 .current otherFileRef) "on another file" ]

def draftComment : Comment :=
  { ref := ⟨"draft-1"⟩, backendId := none, location := .topLevel, isPublished := false,
    author := "alice", createdTimestamp := 7, updatedTimestamp := 7, parent := none,
    replyToId := none, content := "" }

def emptyFileManager : ModifiedFileManager := ⟨Std.HashMap.emptyWithCapacity, [], by simp, by simp⟩

def emptyFileState : ModifiedFileState :=
  { ref := modifiedFileRef, fileRef := ⟨"src/main.c"⟩, selectedComment := none,
    baseThreads := CommentThreads.empty, currentThreads := CommentThreads.empty,
    hSelectedCommentWellFormed := by simp,
    hBaseThreadsFileScoped := by simp [CommentThreads.empty],
    hCurrentThreadsFileScoped := by simp [CommentThreads.empty] }

/-- A selection built from a live lookup is well-formed.

`hCommentTreeNodeRootMatchesKey` says the node stored at `ref` is rooted at `ref`, so the selected
comment is that thread's root. -/
theorem wellFormedSelection {threads : CommentThreads} {ref : CommentRef}
    (h : threads.commentTreeNodes.contains ref) {thread : CommentThread}
    (hthread : threads.commentTreeNodes.get ref h = thread) (version : FileVersion) :
    SelectedComment.WellFormed threads ⟨version, thread, ref⟩ := by
  have hvalue : thread.value = ref := by
    rw [← hthread]
    exact threads.hCommentTreeNodeRootMatchesKey ref h
  subst hvalue
  exact ⟨h, hthread, .refl _⟩

/-- A configuration whose `getRemoteConversations` hands back `comments`.

`configurationElisp` below is its counterpart on the elisp side: `Configuration` has two function
fields, and a Lean closure cannot be rendered into elisp source, so this one fixture is the single
place where the two sides are written out separately and have to be kept in step by hand. -/
def configuration (comments : List Comment) : Configuration :=
  { user := "alice", changesetId := "cs-1", repositories := [], author := "bob", createdAt := 42,
    status := ⟨"open"⟩, changesetUrl := "https://example.com/1", changesetTitle := "A change",
    changesetDescription := "It changes things.",
    createComment := fun _ => some ⟨"sid-new"⟩,
    getRemoteConversations := fun _ => some comments }

def configurationElisp (comments : List Comment) : String :=
  elispCall "make-lgtm-configuration"
    [ toElisp "alice", toElisp "cs-1", "nil", toElisp "bob", "42",
      elispCall "make-lgtm--changeset-status" [toElisp "open"],
      toElisp "https://example.com/1", toElisp "A change", toElisp "It changes things.",
      "(lambda (comment) (make-lgtm--server-id \"sid-new\"))",
      s!"(lambda (file-manager) {toElisp comments})" ]

/-- A review state that has not loaded any comments yet, and is not editing one. -/
def initialState (comments : List Comment) : State :=
  { configuration := configuration comments, activeReviewedFile := none,
    commentBeingEdited := none, commentManager := CommentManager.empty,
    fileManager := emptyFileManager,
    hCommentBeingEditedWellFormed := by simp,
    hFileThreadsPublished := by intro fileRef h; simp [emptyFileManager] at h }

def initialStateElisp (comments : List Comment) : String :=
  elispCall "make-lgtm--state"
    [ configurationElisp comments, "nil", "nil", "lgtm--comment-manager-empty",
      toElisp emptyFileManager ]

/-- A review state part-way through writing a new top-level comment. `draftComment` is fresh
(unknown to the empty `CommentManager`), unpublished and has no parent, which is exactly the
well-formedness `completeCommentWithContent` asks for. -/
def editingState : State :=
  { configuration := configuration topLevelComments, activeReviewedFile := none,
    commentBeingEdited := some draftComment, commentManager := CommentManager.empty,
    fileManager := emptyFileManager,
    hCommentBeingEditedWellFormed := by
      intro comment hcomment
      simp only [Option.some.injEq] at hcomment
      subst hcomment
      refine ⟨by simp [CommentManager.empty], rfl, ?_⟩
      intro parentId hparent
      simp [draftComment] at hparent,
    hFileThreadsPublished := by intro fileRef h; simp [emptyFileManager] at h }

def editingStateElisp : String :=
  elispCall "make-lgtm--state"
    [ configurationElisp topLevelComments, "nil", toElisp draftComment, "lgtm--comment-manager-empty",
      toElisp emptyFileManager ]

/-- The state map of a review that tracks exactly one file. An `abbrev` so that the `Std.HashMap`
lemmas below apply to it without an unfolding step. -/
abbrev singleFileState : Std.HashMap ModifiedFileRef ModifiedFileState :=
  Std.HashMap.emptyWithCapacity.insert modifiedFileRef emptyFileState

theorem contains_singleFileState {ref : ModifiedFileRef} (h : singleFileState.contains ref) :
    ref = modifiedFileRef := by
  rw [Std.HashMap.contains_insert] at h
  simp at h
  exact h.symm

theorem get_singleFileState {ref : ModifiedFileRef} (h : singleFileState.contains ref) :
    singleFileState.get ref h = emptyFileState := by
  have href := contains_singleFileState h
  subst href
  rw [Std.HashMap.get_insert_self]

def singleFileManager : ModifiedFileManager :=
  { state := singleFileState, modifiedFiles := [modifiedFileRef],
    hConsistentState := by
      intro modifiedFile
      constructor
      · intro hmem
        simp only [List.mem_singleton] at hmem
        subst hmem
        exact Std.HashMap.contains_insert_self
      · intro hcontains
        simp [contains_singleFileState hcontains],
    hStateKeyedByRef := by
      intro ref h
      rw [get_singleFileState h]
      exact (contains_singleFileState h).symm }

/-- Comments attached to the tracked file, in both of its versions. -/
def fileComments : List Comment :=
  [ mkComment "b1" "sb1" none 10 (fileLoc 12 .base) "on the base version",
    mkComment "b2" "sb2" (some "sb1") 20 (fileLoc 12 .base) "a reply on the base version",
    mkComment "f1" "sf1" none 30 (fileLoc 7) "on the current version" ]

/-- A review state that tracks one file (and so can accept comments attached to it), with no
comments loaded yet. -/
def fileReviewState (comments : List Comment) : State :=
  { configuration := configuration comments, activeReviewedFile := some modifiedFileRef,
    commentBeingEdited := none, commentManager := CommentManager.empty,
    fileManager := singleFileManager,
    hCommentBeingEditedWellFormed := by simp,
    hFileThreadsPublished := by
      intro modifiedFileRef' h
      have hget : singleFileManager.state.get modifiedFileRef' h = emptyFileState :=
        get_singleFileState h
      rw [hget]
      simp [emptyFileState, CommentThreads.empty] }

def fileReviewStateElisp (comments : List Comment) : String :=
  elispCall "make-lgtm--state"
    [ configurationElisp comments, toElisp modifiedFileRef, "nil", "lgtm--comment-manager-empty",
      toElisp singleFileManager ]

end Fixtures

/-! ## The checks

Each group targets a translation feature as much as a function: literals and `pcase` over nullary
constructors, `Option`, tuples-as-vectors, hash tables, recursion, closures, and the invariant-
carrying structures whose proof fields have to disappear entirely. -/

namespace Checks

open Fixtures

/-- Literals, `Option` results, and `pcase` over an enum -- both directions. -/
def literalChecks : List ElispCheck :=
  [ check1 "lgtm--format-file-modification-type" formatFileModificationType .modified,
    check1 "lgtm--format-file-modification-type" formatFileModificationType .added,
    check1 "lgtm--format-file-modification-type" formatFileModificationType .deleted,
    check1 "lgtm--format-file-modification-type" formatFileModificationType .renamed,
    check1 "lgtm--format-file-modification-type" formatFileModificationType .copied,
    check1 "lgtm--format-file-modification-type" formatFileModificationType .typechange,
    check1 "lgtm--parse-file-modification-type" parseFileModificationType 'M',
    check1 "lgtm--parse-file-modification-type" parseFileModificationType 'R',
    check1 "lgtm--parse-file-modification-type" parseFileModificationType 'T',
    -- Neither of these parses; the second also exercises a character that needs escaping in
    -- elisp's `?c` syntax.
    check1 "lgtm--parse-file-modification-type" parseFileModificationType 'Z',
    check1 "lgtm--parse-file-modification-type" parseFileModificationType ' ' ]

/-- Small total functions over the core types: enums with fields, `Option`, tuples. -/
def coreChecks : List ElispCheck :=
  [ checkBool1 "lgtm--thread-location-is-top-level" ThreadLocation.isTopLevel .topLevel,
    checkBool1 "lgtm--thread-location-is-top-level" ThreadLocation.isTopLevel (.lineNumber 42),
    checkBool1 "lgtm--comment-location-is-top-level" CommentLocation.isTopLevel .topLevel,
    checkBool1 "lgtm--comment-location-is-top-level" CommentLocation.isTopLevel (fileLoc 12),
    check1 "lgtm--comment-location-as-thread-location" CommentLocation.asThreadLocation .topLevel,
    check1 "lgtm--comment-location-as-thread-location" CommentLocation.asThreadLocation (fileLoc 12),
    checkBool1 "lgtm--comment-is-persisted-to-server" Comment.isPersistedToServer topLevelComments[0]!,
    checkBool1 "lgtm--comment-is-persisted-to-server" Comment.isPersistedToServer draftComment,
    -- `compareThreadLocations` matches on a *pair*, so it is where a mismatch between how tuples
    -- are built and how they are matched shows up.
    checkBool2 "lgtm--compare-thread-locations" compareThreadLocations .topLevel (.lineNumber 3),
    checkBool2 "lgtm--compare-thread-locations" compareThreadLocations (.lineNumber 3) .topLevel,
    checkBool2 "lgtm--compare-thread-locations" compareThreadLocations (.lineNumber 3) (.lineNumber 9),
    checkBool2 "lgtm--compare-thread-locations" compareThreadLocations (.lineNumber 9) (.lineNumber 3),
    checkBool2 "lgtm--compare-located-comment-threads" compareLocatedCommentThreads
      (.lineNumber 3, []) (.lineNumber 9, []),
    check2 "lgtm--tree-add-child" Tree.addChild (⟨⟨"c1"⟩, [⟨"c2"⟩]⟩ : CommentThread) ⟨"c3"⟩,
    check3 "lgtm--add-to-list-at" (addToListAt (α := ThreadLocation) (β := CommentRef))
      (.lineNumber 3) ⟨"c1"⟩ Std.HashMap.emptyWithCapacity,
    check3 "lgtm--add-to-list-at" (addToListAt (α := ThreadLocation) (β := CommentRef))
      (.lineNumber 3) ⟨"c2"⟩ (Std.HashMap.emptyWithCapacity.insert (.lineNumber 3) [⟨"c1"⟩]) ]

/-- The `Bool`-valued batch checks: recursion, `List.all`/`any`, and `BEq` on structures. -/
def batchCheckChecks : List ElispCheck :=
  [ checkBool1 "lgtm--check-refs-nodup" checkRefsNodup [⟨"a"⟩, ⟨"b"⟩, ⟨"c"⟩],
    checkBool1 "lgtm--check-refs-nodup" checkRefsNodup [⟨"a"⟩, ⟨"b"⟩, ⟨"a"⟩],
    checkBool1 "lgtm--check-comment-refs-nodup" checkCommentRefsNodup topLevelComments,
    checkBool1 "lgtm--check-comment-refs-nodup" checkCommentRefsNodup (topLevelComments ++ topLevelComments),
    checkBool1 "lgtm--check-all-comments-have-backend-id" checkAllCommentsHaveBackendId topLevelComments,
    checkBool1 "lgtm--check-all-comments-have-backend-id" checkAllCommentsHaveBackendId
      (draftComment :: topLevelComments),
    checkBool1 "lgtm--check-all-parents-in-comments" checkAllParentsInComments topLevelComments,
    -- The reply's parent is missing from this batch.
    checkBool1 "lgtm--check-all-parents-in-comments" checkAllParentsInComments [topLevelComments[1]!],
    checkBool1 "lgtm--check-parents-created-before" checkParentsCreatedBefore topLevelComments,
    checkBool1 "lgtm--check-parents-created-before" checkParentsCreatedBefore
      [topLevelComments[1]!, mkComment "c1" "s1" none 500 .topLevel "created after its reply"],
    checkBool1 "lgtm--check-comment-batch" checkCommentBatch topLevelComments,
    checkBool1 "lgtm--check-comment-batch" checkCommentBatch mixedComments,
    checkBool2 "lgtm--check-file-comment-batches" checkFileCommentBatches
      (Std.HashMap.emptyWithCapacity.insert modifiedFileRef emptyFileState)
      [(modifiedFileRef, topLevelComments)],
    -- The entry names a file the manager doesn't track.
    checkBool2 "lgtm--check-file-comment-batches" checkFileCommentBatches
      (Std.HashMap.emptyWithCapacity.insert modifiedFileRef emptyFileState)
      [(otherFileRef, topLevelComments)] ]

/-- The `deriving DecidableEq` instances, none of which should reach the output.

A `Decidable` value is real run-time data, so `isErasableType` keeps it and `isCompilerGenerated`
exempts `Decidable`-returning declarations from its "the compiler wrote this" heuristics. But the
positions these instances actually occupy in `LgtmLean` are all erased typeclass dictionaries
(`Std.HashMap`'s `[BEq]`/`[Hashable]`, `==`), which lower to elisp `equal` and `:test #'equal`
instead. That leaves the instances referring only to each other, so `pruneToReachable` drops the
lot; `checkDecEq` exists for the day a call site branches on one directly. -/
def decidableEqChecks : List ElispCheck :=
  [ checkPruned "lgtm--inst-decidable-eq-comment-ref-dec-eq",
    checkPruned "lgtm--inst-decidable-eq-server-id-dec-eq",
    checkPruned "lgtm--inst-decidable-eq-git-revision-dec-eq",
    checkPruned "lgtm--inst-decidable-eq-git-revision",
    checkPruned "lgtm--inst-decidable-eq-file-version",
    checkPruned "lgtm--inst-decidable-eq-modification-type",
    checkPruned "lgtm--inst-decidable-eq-thread-location-dec-eq",
    checkPruned "lgtm--inst-decidable-eq-repository-ref-dec-eq",
    checkPruned "lgtm--inst-decidable-eq-modified-file-ref-dec-eq",
    -- Nothing references it, in Lean or in the output, so the exemption alone no longer keeps it.
    checkPruned "lgtm--exists-file-location-version-decidable" ]

/-- Grouping a batch: hash tables keyed by a structure, and lists nested inside them. -/
def groupingChecks : List ElispCheck :=
  [ check1 "lgtm--comments-by-ref" commentsByRef topLevelComments,
    check1 "lgtm--comments-by-ref" commentsByRef mixedComments,
    check1 "lgtm--group-comments" groupComments topLevelComments,
    check1 "lgtm--group-comments" groupComments mixedComments,
    check1 "lgtm--comment-bootstrap-state-all-comments" CommentBootstrapState.allComments
      (groupComments topLevelComments) ]

/-- Per-file state: the accessors a file's threads are read and written through. -/
def fileStateChecks : List ElispCheck :=
  [ check2 "lgtm--modified-file-state-threads-for" ModifiedFileState.threadsFor emptyFileState .base,
    check2 "lgtm--modified-file-state-threads-for" ModifiedFileState.threadsFor emptyFileState .current,
    check1 "lgtm--modified-file-manager-reset-file-state" ModifiedFileManager.resetFileState emptyFileState,
    check1 "lgtm--modified-file-manager-reset-comment-state" ModifiedFileManager.resetCommentState
      emptyFileManager ]

/-- Loading comments that belong to a file rather than to the changeset as a whole: the
per-file fold (`applyBaseThreads`/`applyCurrentThreads`) and the accessors it updates each file's
`ModifiedFileState` through. -/
def fileThreadChecks : List ElispCheck :=
  let loaded := addRemoteComments (fileReviewState fileComments)
  let loadedStateElisp :=
    elispCall "lgtm-result-updated-state"
      [elispCall "lgtm-add-remote-comments" [fileReviewStateElisp fileComments]]
  let fileManager := loaded.updatedState.fileManager
  let baseChecks :=
    if h : fileManager.state.contains modifiedFileRef then
      let fileState := fileManager.state.get modifiedFileRef h
      [ check2 "lgtm--modified-file-state-threads-for" ModifiedFileState.threadsFor fileState .base,
        check2 "lgtm--modified-file-state-threads-for" ModifiedFileState.threadsFor fileState .current,
        check "lgtm--modified-file-state-with-threads-for"
          (elispCall "lgtm--modified-file-state-with-threads-for"
            [toElisp fileState, toElisp FileVersion.current, toElisp fileState.baseThreads])
          (fileState.withThreadsFor .current fileState.baseThreads fileState.hBaseThreadsFileScoped),
        check1 "lgtm--modified-file-manager-reset-comment-state" ModifiedFileManager.resetCommentState
          fileManager ]
    else
      [missingFixture "a loaded ModifiedFileState for the tracked file"]
  [ check "lgtm-add-remote-comments (value, file-scoped)"
      (elispCall "lgtm-result-value"
        [elispCall "lgtm-add-remote-comments" [fileReviewStateElisp fileComments]])
      loaded.value,
    check "lgtm-add-remote-comments (file manager)"
      (elispCall "lgtm--state-file-manager" [loadedStateElisp]) fileManager,
    check "lgtm-add-remote-comments (comment manager, file-scoped)"
      (elispCall "lgtm--state-comment-manager" [loadedStateElisp]) loaded.updatedState.commentManager,
    -- `mixedComments` mentions a file the review doesn't track, so the batch has to be rejected --
    -- leaving the state alone -- rather than loaded.
    check "lgtm-add-remote-comments (untracked file)"
      (elispCall "lgtm-result-value"
        [elispCall "lgtm-add-remote-comments" [fileReviewStateElisp mixedComments]])
      (addRemoteComments (fileReviewState mixedComments)).value,
    checkBool2 "lgtm--check-file-comment-batches" checkFileCommentBatches singleFileState
      [(modifiedFileRef, fileComments)] ] ++ baseChecks

/-- Assembling threads from a batch of comments, and everything that reads the result.

`addRemoteComments` supplies the `CommentThreads`/`CommentManager` the rest of the group is
exercised against, so these values come out of the same pipeline the UI uses. -/
def threadChecks : List ElispCheck :=
  let loadResult := addRemoteComments (initialState topLevelComments)
  let loadedState := loadResult.updatedState
  let manager := loadedState.commentManager
  let threads := manager.topLevelThreads
  let loadedStateElisp :=
    elispCall "lgtm-result-updated-state"
      [elispCall "lgtm-add-remote-comments" [initialStateElisp topLevelComments]]
  let managerElisp := elispCall "lgtm--state-comment-manager" [loadedStateElisp]
  [ check "lgtm-add-remote-comments (value)"
      (elispCall "lgtm-result-value"
        [elispCall "lgtm-add-remote-comments" [initialStateElisp topLevelComments]])
      loadResult.value,
    check "lgtm-add-remote-comments (comment manager)" managerElisp manager,
    check "lgtm-reset-comment-state"
      (elispCall "lgtm--state-comment-manager"
        [elispCall "lgtm-result-updated-state" [elispCall "lgtm-reset-comment-state" [loadedStateElisp]]])
      (resetCommentState loadedState).updatedState.commentManager,
    check2 "lgtm--comment-manager-get" CommentManager.get manager ⟨"c2"⟩,
    checkBool1 "lgtm--comment-threads-is-empty" CommentThreads.isEmpty threads,
    checkBool1 "lgtm--comment-threads-is-empty" CommentThreads.isEmpty CommentThreads.empty,
    check "lgtm--comment-threads-empty (constant)" "lgtm--comment-threads-empty" CommentThreads.empty,
    check "lgtm--comment-manager-empty (constant)" "lgtm--comment-manager-empty" CommentManager.empty,
    check "lgtm--empty-bootstrap-state (constant)" "lgtm--empty-bootstrap-state" emptyBootstrapState,
    check2 "lgtm--comment-threads-as-alist" CommentThreads.asAlist threads manager,
    check2 "lgtm--comment-threads-to-threads-ordered" CommentThreads.toThreadsOrdered threads manager,
    checkBool3 "lgtm--compare-threads-by-timestamp" compareThreadsByTimestamp manager
      ⟨⟨"c1"⟩, []⟩ ⟨⟨"c3"⟩, []⟩,
    checkBool3 "lgtm--compare-threads-by-timestamp" compareThreadsByTimestamp manager
      ⟨⟨"c3"⟩, []⟩ ⟨⟨"c1"⟩, []⟩ ]

/-- Navigation between threads and within a thread.

`nextCommentInThread`/`previousCommentInThread` take a well-formedness proof about the selection,
which `wellFormedSelection` produces for a selection built from a live lookup. -/
def navigationChecks : List ElispCheck :=
  let manager := (addRemoteComments (initialState topLevelComments)).updatedState.commentManager
  let threads := manager.topLevelThreads
  let rootRef : CommentRef := ⟨"c1"⟩
  if h : threads.commentTreeNodes.contains rootRef then
    let thread := threads.commentTreeNodes.get rootRef h
    let selection : SelectedComment := ⟨.current, thread, rootRef⟩
    let hWF := wellFormedSelection h rfl .current
    [ check3 "lgtm--comment-thread-linearize" CommentThread.linearize thread threads manager,
      check4 "lgtm--comment-threads-next-thread" CommentThreads.nextThread threads manager .current selection,
      check4 "lgtm--comment-threads-previous-thread" CommentThreads.previousThread threads manager .current selection,
      -- A selection from a *different* file version resets to the first/last thread.
      check4 "lgtm--comment-threads-next-thread" CommentThreads.nextThread threads manager .base selection,
      check4 "lgtm--comment-threads-previous-thread" CommentThreads.previousThread threads manager .base selection,
      check "lgtm--comment-threads-next-comment-in-thread"
        (elispCall "lgtm--comment-threads-next-comment-in-thread"
          [toElisp threads, toElisp manager, toElisp selection])
        (threads.nextCommentInThread manager selection hWF),
      check "lgtm--comment-threads-previous-comment-in-thread"
        (elispCall "lgtm--comment-threads-previous-comment-in-thread"
          [toElisp threads, toElisp manager, toElisp selection])
        (threads.previousCommentInThread manager selection hWF) ]
  else
    [missingFixture "a thread node for c1"]

/-- `assembleCommentTrees` on its own, with the preconditions recovered from the runtime check the
way `addRemoteComments` recovers them. -/
def assemblyChecks : List ElispCheck :=
  if hBatch : checkCommentBatch topLevelComments = true then
    let ⟨hBackend, hParents, hNodup, hBefore⟩ := (checkCommentBatch_iff topLevelComments).mp hBatch
    let hSameLocation : commentsAllInSameFileOrAllTopLevel topLevelComments := Or.inl (by decide)
    let assembled := assembleCommentTrees topLevelComments hSameLocation hBackend hParents hNodup hBefore
    let newComment := mkComment "c4" "s4" none 400 .topLevel "a thread added after assembly"
    [ check "lgtm--assemble-comment-trees"
        (elispCall "lgtm--assemble-comment-trees" [toElisp topLevelComments]) assembled,
      check "lgtm--add-comment-to-thread"
        (elispCall "lgtm--add-comment-to-thread" [toElisp CommentThreads.empty, toElisp newComment])
        (addCommentToThread CommentThreads.empty newComment rfl
          (by intro parentId hparent; simp [newComment, mkComment] at hparent)
          (by intro parentId _ hparent; simp [newComment, mkComment] at hparent)
          (by simp [CommentThreads.empty])
          (by simp [CommentThreads.empty])) ]
  else
    [missingFixture "checkCommentBatch topLevelComments"]

/-- Creating a comment: the state transition the "write a comment" UI drives. -/
def commentCreationChecks : List ElispCheck :=
  let published := completeCommentWithContent editingState "a brand new comment"
  let cancelled := cancelCommentCreation editingState
  [ check "lgtm-complete-comment-with-content (value)"
      (elispCall "lgtm-result-value"
        [elispCall "lgtm-complete-comment-with-content" [editingStateElisp, toElisp "a brand new comment"]])
      published.value,
    check "lgtm-complete-comment-with-content (comment manager)"
      (elispCall "lgtm--state-comment-manager"
        [elispCall "lgtm-result-updated-state"
          [elispCall "lgtm-complete-comment-with-content" [editingStateElisp, toElisp "a brand new comment"]]])
      published.updatedState.commentManager,
    check "lgtm-cancel-comment-creation (value)"
      (elispCall "lgtm-result-value" [elispCall "lgtm-cancel-comment-creation" [editingStateElisp]])
      cancelled.value,
    check "lgtm-cancel-comment-creation (comment being edited)"
      (elispCall "lgtm--state-comment-being-edited"
        [elispCall "lgtm-result-updated-state" [elispCall "lgtm-cancel-comment-creation" [editingStateElisp]]])
      cancelled.updatedState.commentBeingEdited ]

end Checks

def allChecks : List ElispCheck :=
  Checks.literalChecks ++ Checks.coreChecks ++ Checks.batchCheckChecks ++
  Checks.decidableEqChecks ++ Checks.groupingChecks ++
  Checks.fileStateChecks ++ Checks.fileThreadChecks ++ Checks.threadChecks ++
  Checks.navigationChecks ++
  Checks.assemblyChecks ++ Checks.commentCreationChecks

/-! ## Driving emacs -/

/-- The harness that runs the checks, loaded into emacs ahead of the generated code. -/
def testHarnessElisp : String := include_str "Extractor/test-harness.el"

def renderChecks (checks : List ElispCheck) : String :=
  let header :=
    ";;; checks.el --- Generated by Test.lean.  Do not edit. -*- lexical-binding: t; -*-\n\n"
  let rendered := checks.zipIdx.map fun (c, i) =>
    s!"(lgtm-test--check {i + 1} {elispString c.name}\n  (lambda () {c.expected})\n  (lambda () {c.actual}))\n"
  header ++ String.join rendered ++ "\n(lgtm-test--finish)\n"

/-- Whether `needle` occurs anywhere in `haystack`. -/
def containsSubstring (haystack needle : String) : Bool := (haystack.splitOn needle).length > 1

/-- Byte-compile warnings that mean the extraction produced elisp that merely *looks* right, and
so are treated as failures: a call to a function that is defined nowhere, a call at the wrong
arity, or a variable that isn't bound where it is used (which is what a mistranslated binding form
turns into). Everything else emacs has to say (docstring width, unused variables) is style. -/
def fatalByteCompileWarnings : List String :=
  ["is not known to be defined", "reference to free variable", "but accepts only", "but requires"]

/-- Run `emacs`, returning its output. An emacs that can't be spawned at all surfaces as a
non-zero exit code here rather than as an exception, so `emacsIsRunnable` checks for that up front
instead of letting it look like a hundred broken checks. -/
def runEmacs (emacs : String) (args : List String) : IO IO.Process.Output := do
  try
    IO.Process.output { cmd := emacs, args := args.toArray }
  catch _ =>
    pure { exitCode := 127, stdout := "", stderr := "" }

def emacsIsRunnable (emacs : String) : IO Bool := do
  pure ((← runEmacs emacs ["--version"]).exitCode == 0)

unsafe def main : IO UInt32 := do
  let (_translations, rendered, postState) ← extractLgtm

  let mut failed := false

  -- 1. Did the extraction give up anywhere?
  let definedSet := Std.HashSet.ofList postState.definedFunctionNames
  let undefinedCalledFuncs := postState.referencedGlobalNames.diff definedSet
  unless postState.opaqueValues.isEmpty do
    failed := true
    IO.eprintln s!"Extraction produced {postState.opaqueValues.length} opaque value(s):"
    for reason in postState.opaqueValues.reverse do
      IO.eprintln s!"  - {reason}"
  unless undefinedCalledFuncs.isEmpty do
    failed := true
    IO.eprintln s!"Extraction produced {undefinedCalledFuncs.size} call(s) to functions that were not defined:"
    for func in undefinedCalledFuncs.toList do
      IO.eprintln s!"  - {func}"

  -- Write out everything emacs needs: the code under test, the harness, and the checks.
  let dir : System.FilePath := ".lake" / "build" / "elisp-test"
  IO.FS.createDirAll dir
  let core := dir / "lgtm-lean-core.el"
  let harness := dir / "test-harness.el"
  let checks := dir / "checks.el"
  renderToFile core rendered
  IO.FS.writeFile harness testHarnessElisp
  IO.FS.writeFile checks (renderChecks allChecks)

  let emacs := (← IO.getEnv "EMACS").getD "emacs"
  unless ← emacsIsRunnable emacs do
    IO.eprintln s!"Could not run '{emacs}'. The elisp tests need emacs on PATH, or the EMACS \
      environment variable pointing at one."
    return 1
  let corePath ← IO.FS.realPath core
  let harnessPath ← IO.FS.realPath harness
  let checksPath ← IO.FS.realPath checks

  -- 2. Is the generated file valid elisp?
  IO.println s!"Byte-compiling {core} .."
  let compiled ← runEmacs emacs
    ["-Q", "--batch", "--eval", s!"(unless (byte-compile-file \"{corePath}\") (kill-emacs 1))"]
  let fatalWarnings := fatalByteCompileWarnings.filter (containsSubstring compiled.stderr)
  if compiled.exitCode ≠ 0 || !fatalWarnings.isEmpty then
    failed := true
    -- Only worth reading when something is actually wrong: a clean compile still has plenty to say
    -- about docstring widths and unused variables.
    IO.print compiled.stdout
    IO.eprint compiled.stderr
    if compiled.exitCode ≠ 0 then
      IO.eprintln "The generated elisp did not compile."
    for warning in fatalWarnings do
      IO.eprintln s!"The generated elisp compiled with a fatal warning ({warning})."
  else
    let warningCount := (compiled.stderr.splitOn "\n").filter (containsSubstring · "Warning:") |>.length
    IO.println s!"  compiled, with {warningCount} non-fatal warning(s)."

  -- 3. Does it compute what the Lean it came from computes?
  IO.println s!"Running {allChecks.length} checks against {emacs} .."
  let ran ← runEmacs emacs
    ["-Q", "--batch", "-l", harnessPath.toString, "-l", corePath.toString, "-l", checksPath.toString]
  IO.print ran.stdout
  IO.eprint ran.stderr
  if ran.exitCode ≠ 0 then
    failed := true

  if failed then
    IO.eprintln s!"Elisp test files left in {dir} for inspection."
    pure 1
  else
    pure 0
