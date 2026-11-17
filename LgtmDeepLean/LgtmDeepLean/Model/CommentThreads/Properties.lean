module

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

Neither conjunct implies the other.  Nothing here proves `Eval` deterministic, so a value by one
derivation does not rule out a `Stuck` derivation whose mismatch premise gives a subexpression some
other value; and `¬Stuck` holds of a body stopped at an `unreachable`. -/

@[expose] public section

/-- The first conjunct: nothing in the body goes wrong.

Eight `let`s walked with `Stuck.not_let`, one form at a time.  The bound expression of each is
refuted by the lemma for its form, and the body of each by the same walk one level in — under an
environment binding the name to *whatever* value the `let`'s expression produced, which is why every
level starts by reading that value off the expression.  Where the expression is a `varRef`, a `lam`
or a field read of one, the reading is an inversion principle; where it is a call, it is the
declaration's result type through `FuncDecl.Apply.hasType`.

Nothing here needs the two `unreachable`s to be unreachable: `Stuck.not_optionMatch_unreachable`
refutes the branch that reaches one by `Stuck.not_unreachable`, whatever the scrutinee did.  What
the index and the length have to be is only that they are `int`s, which is what the arithmetic
forms ask of their operands. -/
private theorem CommentThreads.nextCommentInThread.not_stuck_body {td : TypeDecls} {gs : Globals}
    {threads manager selection thread ref rootRef : Value}
    (hWellTyped : Globals.WellTyped td gs)
    (hDeclares : Model.Declares td gs)
    (hThreadsWF : CommentThreads.WellFormed td threads)
    (hManagerWF : CommentManager.WellFormed td manager)
    (hCovered : CommentThreads.NodesCovered manager threads)
    (hSelection : selection.HasType td (.struct "SelectedComment"))
    (hThread : selection.field? "thread" = some thread)
    (hRef : selection.field? "comment" = some ref)
    (hNode : CommentThreads.node? threads rootRef = some thread) :
    ¬Stuck td (CommentThreads.nextCommentInThread.callEnv gs [threads, manager, selection])
      CommentThreads.nextCommentInThread.body := by
  -- The selection's three fields, at the types `SelectedComment` declares for them.
  obtain ⟨ver, hverField, -⟩ := Value.hasType_field hSelection hDeclares.selectedComment
    (f := "version") (t := .ind "FileVersion") rfl
  have hrefTy : ref.HasType td (.struct "CommentRef") := by
    obtain ⟨w, hw, hwTy⟩ := Value.hasType_field hSelection hDeclares.selectedComment
      (f := "comment") (t := .struct "CommentRef") rfl
    obtain rfl : w = ref := Option.some.inj (hw.symm.trans hRef)
    exact hwTy
  have hthreadTy : thread.HasType td (.struct "CommentThread") :=
    CommentThreads.hasType_node? hDeclares.toDeclaresTypes hThreadsWF hNode
  have hsel : (CommentThreads.nextCommentInThread.callEnv gs
      [threads, manager, selection]).lookup "selection" = some selection := by
    simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
      List.lookup]
  -- `selection.thread`: the thread this call linearizes.
  refine Stuck.not_let (Stuck.not_structGet_varRef hsel hThread) fun v₁ hv₁ => ?_
  rw [Eval.structGet_varRef_eq hsel hThread hv₁]
  -- The call to `linearize`, not stuck by its own progress.
  refine Stuck.not_let (by
    refine Stuck.not_app_global (d := CommentThread.linearize)
      (by simpa [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend,
        Globals.env] using hDeclares.linearize)
      (by simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env,
        List.lookup]) ?_ ?_ ?_
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact Stuck.not_varRef (v := threads) (by simp [CommentThreads.nextCommentInThread,
          FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup, List.lookup])
      · exact Stuck.not_varRef (v := manager) (by simp [CommentThreads.nextCommentInThread,
          FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup, List.lookup])
      · exact Stuck.not_varRef (v := thread) (by simp [Env.lookup, List.lookup])
    · intro vs hlen hev
      obtain ⟨x, y, z, rfl⟩ : ∃ x y z, vs = [x, y, z] := by
        rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | _⟩⟩⟩ <;> simp_all
      have hx := Eval.varRef_inv (hev (Expression.varRef "threads", x) (by simp))
      have hy := Eval.varRef_inv (hev (Expression.varRef "manager", y) (by simp))
      have hz := Eval.varRef_inv (hev (Expression.varRef "selectedThread", z) (by simp))
      simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env,
        Env.lookup, List.lookup] at hx hy hz
      subst hx
      subst hy
      subst hz
      exact .cons "threads" hThreadsWF.hasType
        (.cons "manager" hManagerWF.hasType (.cons "thread" hthreadTy .nil))
    · intro vs hlen hev
      obtain ⟨x, y, z, rfl⟩ : ∃ x y z, vs = [x, y, z] := by
        rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | _⟩⟩⟩ <;> simp_all
      have hx := Eval.varRef_inv (hev (Expression.varRef "threads", x) (by simp))
      have hy := Eval.varRef_inv (hev (Expression.varRef "manager", y) (by simp))
      have hz := Eval.varRef_inv (hev (Expression.varRef "selectedThread", z) (by simp))
      simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env,
        Env.lookup, List.lookup] at hx hy hz
      subst hx
      subst hy
      subst hz
      simpa [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env] using
        CommentThread.linearize.not_stuck_body hWellTyped hDeclares hThreadsWF hManagerWF hCovered
          hNode) fun v₂ hv₂ => ?_
  -- What that call returned is a list of comments, by the result type `linearize` declares.
  obtain ⟨vs₂, -, -, happly₂⟩ :=
    FuncDecl.apply_of_eval_app
      (by simpa [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend,
        Globals.env] using hDeclares.linearize)
      (by simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env,
        List.lookup]) hv₂
  have happly₂' : CommentThread.linearize.Apply td gs vs₂ v₂ := by
    simpa [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env] using
      happly₂
  obtain ⟨cs, rfl, hcsTy⟩ := Value.eq_list_of_hasType
    (happly₂'.hasType hWellTyped (hWellTyped _ _ hDeclares.linearize))
  -- The mapping that reads each comment's ref.
  refine Stuck.not_let (by
    refine Stuck.not_listMap
      (Stuck.not_varRef (v := Value.list cs) (by simp [Env.lookup, List.lookup]))
      Stuck.not_lam (fun u hu => ?_) (fun u hu => ?_)
      (fun vs cb cg ps body hel hfl w hw => ?_)
    · have hu' := Eval.varRef_inv hu
      simp [Env.lookup, List.lookup] at hu'
      subst hu'
      exact ⟨_, rfl⟩
    · obtain rfl := Eval.lam_inv hu
      exact ⟨_, _, _, _, rfl⟩
    · obtain rfl : cs = vs := by
        have hel' := Eval.varRef_inv hel
        simp [Env.lookup, List.lookup] at hel'
        simpa using hel'
      obtain ⟨rfl, rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ ∧ _ := by
        simpa [Env.closure, Value.closure.injEq] using Eval.lam_inv hfl
      obtain ⟨rv, hrv, -⟩ := Value.hasType_field (hcsTy w hw) hDeclares.comment
        (f := "ref") (t := .struct "CommentRef") rfl
      exact ⟨.cons "c" (hcsTy w hw) .nil,
        Stuck.not_structGet_varRef (by simp [Env.extend, Env.lookup]) hrv⟩) fun v₃ hv₃ => ?_
  -- And what *it* returned is one ref per comment, each a `CommentRef`.
  obtain ⟨cs', refs, cb₃, cg₃, ps₃, body₃, hel₃, hfl₃, hlen₃, hev₃, rfl⟩ := Eval.listMap_inv hv₃
  obtain rfl : cs = cs' := by
    have h := Eval.varRef_inv hel₃
    simp [Env.lookup, List.lookup] at h
    simpa using h
  obtain ⟨rfl, rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ ∧ _ := by
    simpa [Env.closure, Value.closure.injEq] using Eval.lam_inv hfl₃
  have hrefsField : ∀ p ∈ cs.zip refs, p.1.field? "ref" = some p.2 := by
    intro p hp
    obtain ⟨name, fvs, hc, hf⟩ := Eval.structGet_inv (hev₃ p hp)
    have hcv := Eval.varRef_inv hc
    simp [Env.extend, Env.lookup] at hcv
    rw [hcv]
    simpa [Value.field?] using hf
  have hrefsTy : ∀ w ∈ refs, w.HasType td (.struct "CommentRef") := by
    intro w hw
    obtain ⟨c, hp⟩ := exists_mem_zip_of_mem_right hlen₃ hw
    obtain ⟨rv, hrv, hrvTy⟩ := Value.hasType_field (hcsTy c (List.of_mem_zip hp).1)
      hDeclares.comment (f := "ref") (t := .struct "CommentRef") rfl
    obtain rfl : rv = w := Option.some.inj (hrv.symm.trans (hrefsField (c, w) hp))
    exact hrvTy
  -- `selection.comment`: the ref the search looks for.
  refine Stuck.not_let (Stuck.not_structGet_varRef (by
    simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
      List.lookup]) hRef) fun v₄ hv₄ => ?_
  rw [Eval.structGet_varRef_eq (by simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv,
    Env.extend, Globals.env, Env.lookup, List.lookup]) hRef hv₄]
  -- The predicate the search runs, and the search itself.
  refine Stuck.not_let Stuck.not_lam fun mf hmf => ?_
  have hmfEq := Eval.lam_inv hmf
  refine Stuck.not_let (by
    refine Stuck.not_optionMatch_unreachable ?_ (fun u hu => Eval.isOption_listFindIndex hu)
      fun w hw => Stuck.not_varRef (v := w) (by simp [Env.lookup, List.lookup])
    refine Stuck.not_listFindIndex
      (Stuck.not_varRef (v := Value.list refs) (by simp [Env.lookup, List.lookup]))
      (Stuck.not_varRef (v := mf) (by simp [Env.lookup, List.lookup]))
      (fun u hu => ?_) (fun u hu => ?_) (fun vs cb cg ps body hel hfl w hw => ?_)
    · have hu' := Eval.varRef_inv hu
      simp [Env.lookup, List.lookup] at hu'
      subst hu'
      exact ⟨_, rfl⟩
    · have hu' := Eval.varRef_inv hu
      simp [Env.lookup, List.lookup, hmfEq] at hu'
      subst hu'
      exact ⟨_, _, _, _, rfl⟩
    · obtain rfl : refs = vs := by
        have hel' := Eval.varRef_inv hel
        simp [Env.lookup, List.lookup] at hel'
        simpa using hel'
      obtain ⟨rfl, rfl, rfl, rfl⟩ : _ ∧ _ ∧ _ ∧ _ := by
        simpa [Env.lookup, List.lookup, hmfEq, Env.closure, Value.closure.injEq] using
          Eval.varRef_inv hfl
      refine ⟨.cons "ref" (hrefsTy w hw) .nil, ?_, fun u hu => Eval.isBool_equals hu⟩
      refine Stuck.not_equals (Stuck.not_varRef (v := w) (by simp [Env.extend, Env.lookup]))
        (Stuck.not_varRef (v := ref) (by simp [Env.extend, Env.lookup, List.lookup]))
        fun u₁ u₂ h₁ h₂ => ?_
      have h₁' := Eval.varRef_inv h₁
      have h₂' := Eval.varRef_inv h₂
      simp [Env.extend, Env.lookup, List.lookup] at h₁' h₂'
      subst h₁'
      subst h₂'
      obtain ⟨b, hb, -⟩ := CommentRef.beq?_eq_some hDeclares.commentRef (hrefsTy w hw) hrefTy
      simp [hb]) fun v₆ hv₆ => ?_
  -- What the search answered is an index, which is all the arithmetic below asks of it.
  obtain ⟨w₆, hscrut₆, hbound₆⟩ := Eval.optionMatch_unreachable_inv hv₆
  have hb₆ := Eval.varRef_inv hbound₆
  simp [Env.lookup, List.lookup] at hb₆
  subst hb₆
  obtain ⟨k, rfl⟩ : ∃ k : Int, w₆ = .int k := by
    obtain ⟨vs₆, cb₆, cg₆, ps₆, body₆, hel₆, -, hcase⟩ := Eval.listFindIndex_inv hscrut₆
    rcases hcase with ⟨pre, wsel, post, -, -, -, hval⟩ | ⟨-, hval⟩
    · exact ⟨(pre.length : Int), by simpa using hval⟩
    · simp at hval
  -- The index of the next comment: arithmetic over that index and the list's length.
  refine Stuck.not_let (by
    refine Stuck.not_min ?_ ?_ (fun u hu => ?_) (fun u hu => ?_)
    · refine Stuck.not_plus (Stuck.not_varRef (v := Value.int k) (by simp [Env.lookup,
        List.lookup])) Stuck.not_intLit (fun u hu => ?_) (fun u hu => ?_)
      · have hu' := Eval.varRef_inv hu
        simp [Env.lookup, List.lookup] at hu'
        subst hu'
        exact ⟨_, rfl⟩
      · rw [Eval.intLit_inv hu]
        exact ⟨_, rfl⟩
    · refine Stuck.not_minus (Stuck.not_listLength (Stuck.not_varRef (v := Value.list refs)
        (by simp [Env.lookup, List.lookup])) (fun u hu => ?_)) Stuck.not_intLit
        (fun u hu => ?_) (fun u hu => ?_)
      · have hu' := Eval.varRef_inv hu
        simp [Env.lookup, List.lookup] at hu'
        subst hu'
        exact ⟨_, rfl⟩
      · obtain ⟨-, -, rfl⟩ := Eval.listLength_inv hu
        exact ⟨_, rfl⟩
      · rw [Eval.intLit_inv hu]
        exact ⟨_, rfl⟩
    · obtain ⟨-, -, -, -, rfl⟩ := Eval.plus_inv hu
      exact ⟨_, rfl⟩
    · obtain ⟨-, -, -, -, rfl⟩ := Eval.minus_inv hu
      exact ⟨_, rfl⟩) fun v₇ hv₇ => ?_
  obtain ⟨n, rfl⟩ : ∃ n : Int, v₇ = .int n := by
    obtain ⟨-, -, -, -, rfl⟩ := Eval.min_inv hv₇
    exact ⟨_, rfl⟩
  -- The ref at that index.
  refine Stuck.not_let (by
    refine Stuck.not_optionMatch_unreachable
      (Stuck.not_listIndex
        (Stuck.not_varRef (v := Value.list refs) (by simp [Env.lookup, List.lookup]))
        (Stuck.not_varRef (v := Value.int n) (by simp [Env.lookup, List.lookup]))
        (fun u hu => ?_) (fun u hu => ?_))
      (fun u hu => Eval.isOption_listIndex hu)
      fun w hw => Stuck.not_varRef (v := w) (by simp [Env.lookup, List.lookup])
    · have hu' := Eval.varRef_inv hu
      simp [Env.lookup, List.lookup] at hu'
      subst hu'
      exact ⟨_, rfl⟩
    · have hu' := Eval.varRef_inv hu
      simp [Env.lookup, List.lookup] at hu'
      subst hu'
      exact ⟨_, rfl⟩) fun v₈ hv₈ => ?_
  -- And the selection it answers with, which is stuck exactly where one of its fields is.
  refine Stuck.not_structNew fun p hp => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact Stuck.not_structGet_varRef (by simp [CommentThreads.nextCommentInThread,
      FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup, List.lookup]) hverField
  · exact Stuck.not_structGet_varRef (by simp [CommentThreads.nextCommentInThread,
      FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup, List.lookup]) hThread
  · exact Stuck.not_varRef (v := v₈) (by simp [Env.lookup, List.lookup])

/-- The second conjunct: a call has a value, which is where the two `unreachable`s are paid for.

`Eval` has no rule for the form, so building a derivation *is* showing neither branch that reaches
one is taken.  The search finds an index because the selected ref occurs among the refs of the
linearized thread — `CommentThread.linearize_hasAllThreadComments` at `ref`, with
`hManagerWF.refMatchesKey` to turn the comment the manager holds back into the ref the mapping read
off it — and `exists_first_of_mem` is what turns that into the split `Eval.EListFindIndexSome`
needs.  The index read finds an element because `min (i + 1) (length - 1)` is in range once an index
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
  -- The selection as a struct *value*: this body reads its fields rather than being handed them.
  obtain ⟨selfvs, rfl⟩ := Value.eq_struct_of_hasType hSelection
  have hverF : selfvs.lookup "version" = some ver := by simpa [Value.field?] using hverField
  have hthreadF : selfvs.lookup "thread" = some thread := by simpa [Value.field?] using hThread
  have hrefF : selfvs.lookup "comment" = some ref := by simpa [Value.field?] using hRef
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
  refine Eval.ELet _ _ _ (Eval.EStructGet (name := "SelectedComment") _ _ (Eval.EVarRef _ (by
    simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
      List.lookup])) hthreadF) ?_
  refine Eval.ELet _ _ _ (FuncDecl.eval_app_of_apply (x := "CommentThread.linearize")
    (by simpa [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend,
      Globals.env] using hDeclares.linearize)
    (by simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env,
      List.lookup]) rfl ?args
    (by simpa [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend,
      Globals.env] using happly)) ?_
  case args =>
    intro p hp
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact Eval.EVarRef _ (by simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv,
        Env.extend, Globals.env, Env.lookup, List.lookup])
    · exact Eval.EVarRef _ (by simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv,
        Env.extend, Globals.env, Env.lookup, List.lookup])
    · exact Eval.EVarRef _ (by simp [Env.lookup, List.lookup])
  refine Eval.ELet _ _ _ (Eval.EListMap _ _ (Eval.EVarRef _ (by simp [Env.lookup, List.lookup]))
    (Eval.ELam _ _) hrlen ?argTys ?calls) ?_
  case argTys =>
    intro p hp
    exact .cons "c" (hcsTy p.1 (List.of_mem_zip hp).1) .nil
  case calls =>
    intro p hp
    obtain ⟨cfvs, hcfvs⟩ := Value.eq_struct_of_hasType (hcsTy p.1 (List.of_mem_zip hp).1)
    have hf : cfvs.lookup "ref" = some p.2 := by
      have h := hrall p hp
      rw [hcfvs] at h
      simpa [Value.field?] using h
    rw [hcfvs]
    exact Eval.EStructGet (name := "Comment") _ _
      (Eval.EVarRef _ (by simp [Env.extend, Env.lookup])) hf
  refine Eval.ELet _ _ _ (Eval.EStructGet (name := "SelectedComment") _ _ (Eval.EVarRef _ (by
    simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
      List.lookup])) hrefF) ?_
  refine Eval.ELet _ _ _ (Eval.ELam _ _) ?_
  refine Eval.ELet (v₁ := Value.int (pre.length : Int)) _ _ _
    (Eval.EOptionMatchSome (w := Value.int (pre.length : Int)) _ _ _ _ ?search
      (Eval.EVarRef _ (by simp [Env.lookup, List.lookup]))) ?_
  case search =>
    refine Eval.EListFindIndexSome (pre := pre) (w := ref) (post := post) _ _
      (Eval.EVarRef _ (by rw [← hsplit]; simp [Env.lookup, List.lookup])) (Eval.EVarRef _ rfl)
      ?preTys ?preEv (.cons "ref" hrefTy .nil) ?selEv
    case preTys =>
      intro u hu
      exact .cons "ref" (hrefsTy u (by rw [hsplit]; simp [hu])) .nil
    case preEv =>
      intro u hu
      obtain ⟨b, hb, hiff⟩ := CommentRef.beq?_eq_some hDeclares.commentRef
        (hrefsTy u (by rw [hsplit]; simp [hu])) hrefTy
      obtain rfl : b = false := by
        cases b with
        | false => rfl
        | true => exact absurd (hiff.mp rfl) (hpre u hu)
      exact Eval.EEquals _ _ (Eval.EVarRef _ (by simp [Env.extend, Env.lookup]))
        (Eval.EVarRef _ (by simp [Env.extend, Env.lookup, List.lookup])) hb
    case selEv =>
      obtain ⟨b, hb, hiff⟩ := CommentRef.beq?_eq_some hDeclares.commentRef hrefTy hrefTy
      obtain rfl : b = true := hiff.mpr rfl
      exact Eval.EEquals _ _ (Eval.EVarRef _ (by simp [Env.extend, Env.lookup]))
        (Eval.EVarRef _ (by simp [Env.extend, Env.lookup, List.lookup])) hb
  refine Eval.ELet (v₁ := Value.int (min ((pre.length : Int) + 1) ((refs.length : Int) - 1)))
    _ _ _
    (Eval.EMin _ _
      (Eval.EPlus _ _ (Eval.EVarRef _ (by simp [Env.lookup, List.lookup])) (Eval.EIntLit _))
      (Eval.EMinus _ _ (Eval.EListLength _ (Eval.EVarRef _ (by simp [Env.lookup, List.lookup])))
        (Eval.EIntLit _))) ?_
  refine Eval.ELet (v₁ := rfinal) _ _ _
    (Eval.EOptionMatchSome (w := rfinal) _ _ _ _
      (by
        rw [← hrfinal]
        exact Eval.EListIndex _ _ (Eval.EVarRef _ (by simp [Env.lookup, List.lookup]))
          (Eval.EVarRef _ (by simp [Env.lookup, List.lookup])))
      (Eval.EVarRef _ (by simp [Env.lookup, List.lookup]))) ?_
  refine Eval.EStructNew _ _ rfl ?_
  intro p hp
  simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact Eval.EStructGet (name := "SelectedComment") _ _ (Eval.EVarRef _ (by
      simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env,
        Env.lookup, List.lookup])) hverF
  · exact Eval.EStructGet (name := "SelectedComment") _ _ (Eval.EVarRef _ (by
      simp [CommentThreads.nextCommentInThread, FuncDecl.callEnv, Env.extend, Globals.env,
        Env.lookup, List.lookup])) hthreadF
  · exact Eval.EVarRef _ (by simp [Env.lookup, List.lookup])

/-- `nextCommentInThread` never goes wrong and always answers: no subexpression of its body is
stuck, and a call to it has a value — so neither `unreachable` in it is reached, and the recursion
`CommentThread.linearize` makes terminates.

The first group of hypotheses is what progress alone needs.  `hDeclares` and `hWellTyped` make the
`varRef`s resolve and keep the values flowing through the body well typed — the call to
`CommentThread.linearize` is checked against `gs`, and so is the call to `CommentManager.get` its
body makes in turn.  `hDeclares` also lets the field reads be read at their declared types:
`selection.thread` is a `CommentThread`, which is what the call to `linearize` needs of its third
argument, and `c.ref` is a `CommentRef`, which is what makes the `==` the search runs have an
answer.

The rest is what the second conjunct costs, one hypothesis per `unreachable` reachable without it:

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
      ∃ v, CommentThreads.nextCommentInThread.Apply td gs [threads, manager, selection] v :=
  ⟨CommentThreads.nextCommentInThread.not_stuck_body hWellTyped hDeclares hThreadsWF hManagerWF
      hCovered hSelection hThread hRef hNode,
    CommentThreads.nextCommentInThread.apply_exists hWellTyped hDeclares hThreadsWF hManagerWF
      hCovered hSelection hThread hRef hNode hHasRef⟩

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
      ∃ v, CommentThreads.previousCommentInThread.Apply td gs [threads, manager, selection] v := sorry

end
