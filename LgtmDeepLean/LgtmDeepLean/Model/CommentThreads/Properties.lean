module

public import LgtmDeepLean.Lang.Eval.Yields
public import LgtmDeepLean.Lang.Progress
meta import LgtmDeepLean.Lang.Syntax
public import LgtmDeepLean.Lang.Value
public import LgtmDeepLean.Model.Basic.WellFormed
public import LgtmDeepLean.Model.CommentManager.Properties
public import LgtmDeepLean.Model.CommentThreads.Operations
public import LgtmDeepLean.Model.CommentThreads.Properties.Sorted
public import LgtmDeepLean.Model.Program

/-! # Progress for `CommentThreads.nextCommentInThread` and `previousCommentInThread`

The order `toThreadsOrdered` returns threads in, and the progress of the declarations this one calls
through to the bottom, are in `Properties.Sorted`; the hypotheses here are the ones that module's
docstring describes, and what it proves of `CommentThread.linearize` is what this spends at the call
this body makes.

`Progress` (Lang/Progress.lean) stated of one declaration, and then strengthened past it.  `¬Stuck`
over the body under the environment a call builds is the general property read off this
declaration: nothing it evaluates reaches a form no rule of `Eval` can fire on.  It is silent about
the two other ways an expression has no value — divergence, and an `unreachable` reached — so the
second conjunct says a call has a value after all, which is where the model's invariants are spent.

`Eval` has no rule for `unreachable` (`Eval.not_unreachable`), so a derivation of a value for the
body is itself the proof that neither `unreachable` in it was evaluated: "the unreachables are not
reachable" needs no separate statement, and there is nothing weaker that could be said about them —
an `unreachable` is reached or the call has a value.

The second conjunct implies the first, and that is the whole of what `Eval.unique` buys: a value by
one derivation rules out a `Stuck` derivation, because the value a `Stuck` mismatch premise gave a
subexpression is the one the construction gave it (`Eval.not_stuck`).  The converse fails — `¬Stuck`
holds of a body stopped at an `unreachable` — which is why the second conjunct is the one that has
to be proved. -/

@[expose] public section

/-- The body `nextCommentInThread` and `previousCommentInThread` share, with the index they read the
answer at left open: one computes `min (i + 1) (length - 1)` there and the other `max 0 (i - 1)`,
and nothing else about the two differs.

What holds this to them is that `CommentThreads.commentInThread.apply_exists` is applied to each at
`rfl`, so a change to either body that is not a change to that index stops compiling at the call
rather than leaving the shared proof proving something about a body nothing declares.

The index read is written out rather than spelled `linearizedCommentRefs[nextIndex]`: those brackets
are read by the type of what they index, and a fragment elaborates in no context, so nothing here
would say the read is of a list rather than of a hashmap. -/
private def CommentThreads.commentInThread.body (nextIndex : Expression) : Expression :=
  [lgtm| let selectedThread := selection.thread;
    let linearizedComments := CommentThread.linearize(threads, manager, selectedThread);
    let linearizedCommentRefs := map linearizedComments (fun (c : struct Comment) => c.ref);
    let currentlySelectedRef := selection.comment;
    let matchesSelectedRef := fun (ref : struct CommentRef) => ref == currentlySelectedRef;
    let currentlySelectedIndex := match findIndex linearizedCommentRefs matchesSelectedRef with
      | none => (unreachable "The selected comment must exist in the linearized thread" : int)
      | some(idx) => idx;
    let nextIndex := ~(nextIndex);
    let nextCommentRef :=
      match ~(Expression.listIndex (.varRef "linearizedCommentRefs") (.varRef "nextIndex")) with
      | none => (unreachable "The next comment index must exist in the linearized comment list" : struct CommentRef)
      | some(r) => r;
    new SelectedComment { version = selection.version, thread = selection.thread, comment = nextCommentRef }]

/-- The second conjunct for either declaration: a call has a value, which is where the two
`unreachable`s are paid for.

`Eval` has no rule for the form, so building a derivation *is* showing neither branch that reaches
one is taken.  The search finds an index because the selected ref occurs among the refs of the
linearized thread — `CommentThread.linearize_hasAllThreadComments` at `ref`, with
`hManagerWF.refMatchesKey` to turn the comment the manager holds back into the ref the mapping read
off it — and `exists_first_of_mem` is what turns that into the split
`Eval.Yields.listFindIndex_found` needs.

`CommentRef.beq?_eq_some` is what the `==` costs, three times over: it has an answer at all, it is
`false` at every ref before the selected one, and it is `true` at the selected one.

`hparams` and `hbody` are how a declaration is named; both are `rfl` at a call, and `hbody` is what
stops this being applied to a body it is not the proof of.

The second `unreachable` is the caller's, and it is the only thing that is.  `hIndex` says what the
index the body computes evaluates to at the environment the `let`s before it built, and `hInRange`
says that position is one the list has — of a *found* index `i`, which is all either caller gets to
know about it.  Neither mentions how `i` was found, so neither can be discharged by anything but
arithmetic, which is what makes the split here the whole of the difference between the two. -/
private theorem CommentThreads.commentInThread.apply_exists {td : TypeDecls} {gs : Globals}
    {d : FuncDecl} {nextIndex : Expression} {idxOf : List Value → Int → Int}
    {threads manager selection thread ref rootRef : Value}
    (hparams : d.parameters = [("threads", Ty.struct "CommentThreads"),
      ("manager", .struct "CommentManager"), ("selection", .struct "SelectedComment")])
    (hbody : d.body = CommentThreads.commentInThread.body nextIndex)
    (hWellTyped : Globals.WellTyped td gs)
    (hDeclares : Model.Declares td gs)
    (hThreadsWF : CommentThreads.WellFormed td threads)
    (hManagerWF : CommentManager.WellFormed td manager)
    (hCovered : CommentThreads.NodesCovered manager threads)
    (hSelection : selection.HasType td (.struct "SelectedComment"))
    (hThread : selection.field? "thread" = some thread)
    (hRef : selection.field? "comment" = some ref)
    (hNode : CommentThreads.node? threads rootRef = some thread)
    (hHasRef : CommentThread.HasRef threads thread ref)
    (hIndex : ∀ (refs : List Value) (i : Int) (env : Env), 0 ≤ i → i < (refs.length : Int) →
      env.lookup "linearizedCommentRefs" = some (.list refs) →
      env.lookup "currentlySelectedIndex" = some (.int i) →
      Eval.Yields td env nextIndex (.int (idxOf refs i)))
    (hInRange : ∀ (refs : List Value) (i : Int), 0 ≤ i → i < (refs.length : Int) →
      ∃ w, Value.index? refs (idxOf refs i) = some w) :
    ∃ v, d.Apply td gs [threads, manager, selection] v := by
  obtain ⟨ver, hverField, -⟩ := Value.hasType_field hSelection hDeclares.selectedComment
    (f := "version") (t := .ind "FileVersion") rfl
  have hrefTy : ref.HasType td (.struct "CommentRef") := by
    obtain ⟨w, hw, hwTy⟩ := Value.hasType_field hSelection hDeclares.selectedComment
      (f := "comment") (t := .struct "CommentRef") rfl
    obtain rfl : w = ref := Option.some.inj (hw.symm.trans hRef)
    exact hwTy
  -- The linearized thread, and the comments it holds.
  obtain ⟨cs, happly⟩ :=
    CommentThread.linearize.apply_exists hDeclares hThreadsWF hManagerWF hCovered hNode
  have hcsTy : ∀ w ∈ cs, w.HasType td (.struct "Comment") := by
    cases happly.hasType hWellTyped (hWellTyped _ _ hDeclares.linearize) with
    | list h => exact h
  -- One ref per comment: the list the mapping produces, built from one witness per element.
  obtain ⟨refs, hrlen, hrall⟩ := exists_zip_of_forall_exists (l := cs)
    (P := fun (c r : Value) => c.field? "ref" = some r)
    fun c hc => by
      obtain ⟨rv, hrv, -⟩ := Value.hasType_field (hcsTy c hc) hDeclares.comment
        (f := "ref") (t := .struct "CommentRef") rfl
      exact ⟨rv, hrv⟩
  have hrefsTy : ∀ w ∈ refs, w.HasType td (.struct "CommentRef") := by
    intro w hw
    obtain ⟨c, hp⟩ := exists_mem_zip_of_mem_right hrlen hw
    obtain ⟨rv, hrv, hrvTy⟩ := Value.hasType_field (hcsTy c (List.of_mem_zip hp).1)
      hDeclares.comment (f := "ref") (t := .struct "CommentRef") rfl
    obtain rfl : rv = w := Option.some.inj (hrv.symm.trans (hrall (c, w) hp))
    exact hrvTy
  -- The selected ref is one of them, which is what rules out the first `unreachable`.
  obtain ⟨c₀, hget₀, hmem₀⟩ :=
    CommentThread.linearize_hasAllThreadComments hDeclares happly ref hHasRef
  have hrefMem : ref ∈ refs := by
    obtain ⟨r₀, hp₀⟩ := exists_mem_zip_of_mem_left hrlen hmem₀
    obtain rfl : r₀ = ref := Option.some.inj
      ((hrall (c₀, r₀) hp₀).symm.trans (hManagerWF.refMatchesKey ref c₀ hget₀))
    exact (List.of_mem_zip hp₀).2
  obtain ⟨pre, wsel, post, hsplit, hpre, hwsel⟩ :=
    exists_first_of_mem (fun y => y = ref) hrefMem rfl
  rw [hwsel] at hsplit
  have hlen : refs.length = pre.length + 1 + post.length := by
    rw [hsplit, List.length_append, List.length_cons]
    omega
  -- The index read, at whichever position the body computes: the second `unreachable`.
  obtain ⟨rfinal, hrfinal⟩ := hInRange refs pre.length (by omega) (by omega)
  -- The selection the call answers with: the one it was given, at the ref the index found.
  have hargs : ArgsHaveType td d.parameters [threads, manager, selection] := by
    rw [hparams]
    exact .cons "threads" hThreadsWF.hasType
      (.cons "manager" hManagerWF.hasType (.cons "selection" hSelection .nil))
  refine ⟨.struct "SelectedComment" [("version", ver), ("thread", thread), ("comment", rfinal)],
    .EApply _ hargs ?_⟩
  simp only [hbody, FuncDecl.callEnv, hparams]
  -- `selectedThread`, and the list `linearize` returns for it.
  refine Eval.Yields.let_ (.structGet (.varRef (by yields_lookup)) hThread) ?_
  refine .let_ (.app_global (by yields_lookup using hDeclares.linearize) (by yields_lookup)
    (.cons (.varRef (by yields_lookup)) (.cons (.varRef (by yields_lookup))
      (.cons (.varRef (by yields_lookup)) .nil)))
    (by yields_lookup using happly)) ?_
  -- One ref per comment, read off the comment the mapping was handed.
  refine .let_ (.listMap (.varRef (by yields_lookup)) .lam hrlen ?calls) ?_
  case calls =>
    intro p hp
    have hcTy := hcsTy p.1 (List.of_mem_zip hp).1
    exact ⟨.cons "c" hcTy .nil, .structGet (.varRef (by yields_lookup)) (hrall p hp)⟩
  -- `currentlySelectedRef` and the closure that compares a ref against it.
  refine .let_ (.structGet (.varRef (by yields_lookup)) hRef) ?_
  refine .let_ .lam ?_
  -- `currentlySelectedIndex`: the search finds the selected ref, which is the first `unreachable`.
  refine .let_ (.optionMatch_some
    (.listFindIndex_found (pre := pre) (w := ref) (post := post)
      (.varRef (by rw [← hsplit]; yields_lookup)) (.varRef rfl) ?pre
      (.cons "ref" hrefTy .nil) ?sel)
    (.varRef (by yields_lookup))) ?_
  case pre =>
    intro u hu
    have huTy := hrefsTy u (by rw [hsplit]; simp [hu])
    obtain ⟨b, hb, hiff⟩ := CommentRef.beq?_eq_some hDeclares.commentRef huTy hrefTy
    obtain rfl : b = false := by
      cases b with
      | false => rfl
      | true => exact absurd (hiff.mp rfl) (hpre u hu)
    exact ⟨.cons "ref" huTy .nil,
      .equals (.varRef (by yields_lookup)) (.varRef (by yields_lookup)) hb⟩
  case sel =>
    obtain ⟨b, hb, hiff⟩ := CommentRef.beq?_eq_some hDeclares.commentRef hrefTy hrefTy
    obtain rfl : b = true := hiff.mpr rfl
    exact .equals (.varRef (by yields_lookup)) (.varRef (by yields_lookup)) hb
  -- `nextIndex`, which is the caller's, and the read at it.
  refine .let_ (hIndex refs pre.length _ (by omega) (by omega)
    (by yields_lookup) (by yields_lookup)) ?_
  refine .let_ (.optionMatch_some
    (.listIndex (.varRef (by yields_lookup)) (.varRef (by yields_lookup)) hrfinal)
    (.varRef (by yields_lookup))) ?_
  exact .structNew (.cons "version" (.structGet (.varRef (by yields_lookup)) hverField)
    (.cons "thread" (.structGet (.varRef (by yields_lookup)) hThread)
      (.cons "comment" (.varRef (by yields_lookup)) .nil)))

/-- `nextCommentInThread`'s own share of the construction: the index is
`min (i + 1) (length - 1)`, and it is in range because a found index is in range and the list it was
found in is therefore non-empty — the one step of this proof that is arithmetic rather than
invariant. -/
private theorem CommentThreads.nextCommentInThread.apply_exists {td : TypeDecls} {gs : Globals}
    {threads manager selection thread ref rootRef : Value}
    (hWellTyped : Globals.WellTyped td gs)
    (hDeclares : Model.Declares td gs)
    (hThreadsWF : CommentThreads.WellFormed td threads)
    (hManagerWF : CommentManager.WellFormed td manager)
    (hCovered : CommentThreads.NodesCovered manager threads)
    (hSelection : selection.HasType td (.struct "SelectedComment"))
    (hThread : selection.field? "thread" = some thread)
    (hRef : selection.field? "comment" = some ref)
    (hNode : CommentThreads.node? threads rootRef = some thread)
    (hHasRef : CommentThread.HasRef threads thread ref) :
    ∃ v, CommentThreads.nextCommentInThread.Apply td gs [threads, manager, selection] v :=
  CommentThreads.commentInThread.apply_exists
    (idxOf := fun refs i => min (i + 1) ((refs.length : Int) - 1)) rfl rfl hWellTyped hDeclares
    hThreadsWF hManagerWF hCovered hSelection hThread hRef hNode hHasRef
    (fun _ _ _ _ _ hrefs hidx =>
      .min (.plus (.varRef hidx) .intLit) (.minus (.listLength (.varRef hrefs)) .intLit))
    fun refs i _ _ => by
      have h0 : ¬min (i + 1) ((refs.length : Int) - 1) < 0 := by omega
      have hidx : (min (i + 1) ((refs.length : Int) - 1)).toNat < refs.length := by omega
      exact ⟨refs[(min (i + 1) ((refs.length : Int) - 1)).toNat], by simp [Value.index?, h0]⟩

/-- `nextCommentInThread` never goes wrong and always answers: no subexpression of its body is
stuck, and a call to it has a value — so neither `unreachable` in it is reached, and the recursion
`CommentThread.linearize` makes terminates.

Both conjuncts come out of `CommentThreads.nextCommentInThread.apply_exists`: the second is it, and
the first is it through `Eval.not_stuck`, since an expression with a value does not reach a form no
rule of `Eval` can fire on.  So every hypothesis below is one the *construction* needs.

`hDeclares` and `hWellTyped` make the `varRef`s resolve and keep the values flowing through the body
well typed — the call to `CommentThread.linearize` is checked against `gs`, and so is the call to
`CommentManager.get` its body makes in turn.  `hDeclares` also lets the field reads be read at their
declared types: `selection.thread` is a `CommentThread`, which is what the call to `linearize` needs
of its third argument, and `c.ref` is a `CommentRef`, which is what makes the `==` the search runs
have an answer.

The rest is what the `unreachable`s cost, one hypothesis per `unreachable` reachable without it:

* `hThreadsWF.childrenRegistered` and `hCovered` are `linearize`'s two — a child ref with no node,
  and a node naming a comment the manager does not hold — and `hNode` is what puts the selected
  thread in range of both, since `CommentThreads.NodesCovered` speaks of registered nodes only.
  `hThreadsWF.childEdgeWf` is what makes the recursion over the children well founded, and
  `hManagerWF` is what gives each comment the sort's comparison a timestamp to compare
  (`CommentManager.timestampIsInt`).
* `hHasRef` is this body's own: the selected ref has to occur in the linearized thread for the
  search to find an index, which is `CommentThread.linearize_hasAllThreadComments` at `ref`,
  together with `hManagerWF.refMatchesKey` to turn the comment the manager holds back into the ref
  the map of the result carries.

The index read needs nothing further: a found index is in range and the list is non-empty, so
`min (i + 1) (length - 1)` is in range too, which is the second `unreachable` ruled out by
arithmetic rather than by an invariant. -/
theorem CommentThreads.nextCommentInThread.progress {td : TypeDecls} {gs : Globals}
    {threads manager selection thread ref rootRef : Value}
    (hDeclares : Model.Declares td gs)
    (hWellTyped : Globals.WellTyped td gs)
    (hThreadsWF : CommentThreads.WellFormed td threads)
    (hManagerWF : CommentManager.WellFormed td manager)
    (hCovered : CommentThreads.NodesCovered manager threads)
    (hSelection : selection.HasType td (.struct "SelectedComment"))
    (hThread : selection.field? "thread" = some thread)
    (hRef : selection.field? "comment" = some ref)
    (hNode : CommentThreads.node? threads rootRef = some thread)
    (hHasRef : CommentThread.HasRef threads thread ref) :
    ¬Stuck td (CommentThreads.nextCommentInThread.callEnv gs [threads, manager, selection])
        CommentThreads.nextCommentInThread.body ∧
      ∃ v, CommentThreads.nextCommentInThread.Apply td gs [threads, manager, selection] v := by
  obtain ⟨v, happly⟩ := CommentThreads.nextCommentInThread.apply_exists hWellTyped hDeclares
    hThreadsWF hManagerWF hCovered hSelection hThread hRef hNode hHasRef
  refine ⟨?_, v, happly⟩
  cases happly with
  | EApply _ _ hbody => exact Eval.not_stuck hbody

/-- `previousCommentInThread`'s own share: the index is `max 0 (i - 1)`, and it is in range because
a found index is and this one is no larger.

Unlike `nextCommentInThread`'s it needs nothing of the list's length, which is why `hIndex` here
does not read `linearizedCommentRefs` — the only asymmetry between the two. -/
private theorem CommentThreads.previousCommentInThread.apply_exists {td : TypeDecls} {gs : Globals}
    {threads manager selection thread ref rootRef : Value}
    (hWellTyped : Globals.WellTyped td gs)
    (hDeclares : Model.Declares td gs)
    (hThreadsWF : CommentThreads.WellFormed td threads)
    (hManagerWF : CommentManager.WellFormed td manager)
    (hCovered : CommentThreads.NodesCovered manager threads)
    (hSelection : selection.HasType td (.struct "SelectedComment"))
    (hThread : selection.field? "thread" = some thread)
    (hRef : selection.field? "comment" = some ref)
    (hNode : CommentThreads.node? threads rootRef = some thread)
    (hHasRef : CommentThread.HasRef threads thread ref) :
    ∃ v, CommentThreads.previousCommentInThread.Apply td gs [threads, manager, selection] v :=
  CommentThreads.commentInThread.apply_exists (idxOf := fun _ i => max 0 (i - 1)) rfl rfl
    hWellTyped hDeclares hThreadsWF hManagerWF hCovered hSelection hThread hRef hNode hHasRef
    (fun _ _ _ _ _ _ hidx => .max .intLit (.minus (.varRef hidx) .intLit))
    fun refs i _ _ => by
      have h0 : ¬max 0 (i - 1) < 0 := by omega
      have hidx : (max 0 (i - 1)).toNat < refs.length := by omega
      exact ⟨refs[(max 0 (i - 1)).toNat], by simp [Value.index?, h0]⟩

/-- `previousCommentInThread` never goes wrong and always answers, for the reasons
`CommentThreads.nextCommentInThread.progress` does: the bodies differ only in the index they read at,
and this one's is in range by arithmetic alone.  Every hypothesis is the same one, spent the same
way. -/
theorem CommentThreads.previousCommentInThread.progress {td : TypeDecls} {gs : Globals}
    {threads manager selection thread ref rootRef : Value}
    (hDeclares : Model.Declares td gs)
    (hWellTyped : Globals.WellTyped td gs)
    (hThreadsWF : CommentThreads.WellFormed td threads)
    (hManagerWF : CommentManager.WellFormed td manager)
    (hCovered : CommentThreads.NodesCovered manager threads)
    (hSelection : selection.HasType td (.struct "SelectedComment"))
    (hThread : selection.field? "thread" = some thread)
    (hRef : selection.field? "comment" = some ref)
    (hNode : CommentThreads.node? threads rootRef = some thread)
    (hHasRef : CommentThread.HasRef threads thread ref) :
    ¬Stuck td (CommentThreads.previousCommentInThread.callEnv gs [threads, manager, selection])
        CommentThreads.previousCommentInThread.body ∧
      ∃ v, CommentThreads.previousCommentInThread.Apply td gs [threads, manager, selection] v := by
  obtain ⟨v, happly⟩ := CommentThreads.previousCommentInThread.apply_exists hWellTyped hDeclares
    hThreadsWF hManagerWF hCovered hSelection hThread hRef hNode hHasRef
  refine ⟨?_, v, happly⟩
  cases happly with
  | EApply _ _ hbody => exact Eval.not_stuck hbody

end
