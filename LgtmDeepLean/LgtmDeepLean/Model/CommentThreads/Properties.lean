module

public import LgtmDeepLean.Lang.Eval.Yields
public import LgtmDeepLean.Lang.Progress
public import LgtmDeepLean.Lang.Value
public import LgtmDeepLean.Model.Basic.WellFormed
public import LgtmDeepLean.Model.CommentManager.Properties
public import LgtmDeepLean.Model.CommentThreads.Operations
public import LgtmDeepLean.Model.CommentThreads.Properties.Sorted
public import LgtmDeepLean.Model.Program

/-! # Progress for `CommentThreads.nextCommentInThread`

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

/-- The second conjunct: a call has a value, which is where the two `unreachable`s are paid for.

`Eval` has no rule for the form, so building a derivation *is* showing neither branch that reaches
one is taken.  The search finds an index because the selected ref occurs among the refs of the
linearized thread — `CommentThread.linearize_hasAllThreadComments` at `ref`, with
`hManagerWF.refMatchesKey` to turn the comment the manager holds back into the ref the mapping read
off it — and `exists_first_of_mem` is what turns that into the split
`Eval.Yields.listFindIndex_found` needs.  The index read finds an element because `min (i + 1) (length - 1)` is in range once an index
was found at all, which is the one step of this proof that is arithmetic rather than invariant.

`CommentRef.beq?_eq_some` is what the `==` costs, three times over: it has an answer at all, it is
`false` at every ref before the selected one, and it is `true` at the selected one. -/
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
    ∃ v, CommentThreads.nextCommentInThread.Apply td gs [threads, manager, selection] v := by
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
  -- A found index and a non-empty list put the next index in range: the second `unreachable`.
  obtain ⟨rfinal, hrfinal⟩ : ∃ r, Value.index? refs
      (min ((pre.length : Int) + 1) ((refs.length : Int) - 1)) = some r := by
    have h0 : ¬min ((pre.length : Int) + 1) ((refs.length : Int) - 1) < 0 := by omega
    have hidx : (min ((pre.length : Int) + 1) ((refs.length : Int) - 1)).toNat < refs.length := by
      omega
    exact ⟨refs[(min ((pre.length : Int) + 1) ((refs.length : Int) - 1)).toNat],
      by simp [Value.index?, h0]⟩
  -- The selection the call answers with: the one it was given, at the ref the index found.
  refine ⟨.struct "SelectedComment" [("version", ver), ("thread", thread), ("comment", rfinal)],
    .EApply _ (.cons "threads" hThreadsWF.hasType
      (.cons "manager" hManagerWF.hasType (.cons "selection" hSelection .nil))) ?_⟩
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
  -- `nextIndex`, and the read at it: a found index and a non-empty list put it in range, which is
  -- the second `unreachable`.
  refine .let_ (by yields) ?_
  refine .let_ (.optionMatch_some
    (.listIndex (.varRef (by yields_lookup)) (.varRef (by yields_lookup)) hrfinal)
    (.varRef (by yields_lookup))) ?_
  exact .structNew (.cons "version" (.structGet (.varRef (by yields_lookup)) hverField)
    (.cons "thread" (.structGet (.varRef (by yields_lookup)) hThread)
      (.cons "comment" (.varRef (by yields_lookup)) .nil)))

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

/-- The second conjunct for `previousCommentInThread`, which is
`CommentThreads.nextCommentInThread.apply_exists` with one step different.

Everything up to the index is the same proof: the same two `unreachable`s, the selected ref found in
the linearized thread by `CommentThread.linearize_hasAllThreadComments`, the same three uses of
`CommentRef.beq?_eq_some`.  What differs is the arithmetic that puts the index read in range —
`max 0 (i - 1)` is in range because `i` is, where `nextCommentInThread` needed the list to be
non-empty as well to know `min (i + 1) (length - 1)` was. -/
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
    ∃ v, CommentThreads.previousCommentInThread.Apply td gs [threads, manager, selection] v := by
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
  -- A found index puts the previous index in range on its own: the second `unreachable`.
  obtain ⟨rfinal, hrfinal⟩ : ∃ r, Value.index? refs (max 0 ((pre.length : Int) - 1)) = some r := by
    have h0 : ¬max 0 ((pre.length : Int) - 1) < 0 := by omega
    have hidx : (max 0 ((pre.length : Int) - 1)).toNat < refs.length := by omega
    exact ⟨refs[(max 0 ((pre.length : Int) - 1)).toNat], by simp [Value.index?, h0]⟩
  -- The selection the call answers with: the one it was given, at the ref the index found.
  refine ⟨.struct "SelectedComment" [("version", ver), ("thread", thread), ("comment", rfinal)],
    .EApply _ (.cons "threads" hThreadsWF.hasType
      (.cons "manager" hManagerWF.hasType (.cons "selection" hSelection .nil))) ?_⟩
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
  -- `nextIndex`, and the read at it: a found index is in range, so the one before it is too, which
  -- is the second `unreachable`.
  refine .let_ (by yields) ?_
  refine .let_ (.optionMatch_some
    (.listIndex (.varRef (by yields_lookup)) (.varRef (by yields_lookup)) hrfinal)
    (.varRef (by yields_lookup))) ?_
  exact .structNew (.cons "version" (.structGet (.varRef (by yields_lookup)) hverField)
    (.cons "thread" (.structGet (.varRef (by yields_lookup)) hThread)
      (.cons "comment" (.varRef (by yields_lookup)) .nil)))

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
