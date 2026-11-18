module

public import LgtmDeepLean.Lang.Eval
public import LgtmDeepLean.Lang.Value
public import LgtmDeepLean.Model.Basic.WellFormed
public import LgtmDeepLean.Model.CommentManager.Operations

/-! # Reading a comment out of the manager

`CommentManager.get` is one `hashmapGet` over one field, which is exactly what
`CommentManager.get?` is: the declaration and the predicate the invariants are stated over agree,
and this is where they are held against each other. -/

@[expose] public section

theorem CommentManager.get.eq_get? {td : TypeDecls} {gs : Globals} {manager ref c : Value}
    (h : CommentManager.get.Apply td gs [manager, ref] (.option (some c))) :
    CommentManager.get? manager ref = some c := by
  obtain ⟨-, -, hbody⟩ := h
  obtain ⟨kvs, vk, hm, hk, hlookup⟩ := Eval.hashmapGet_inv hbody
  obtain ⟨_n, _fvs, hs, hf⟩ := Eval.structGet_inv hm
  have hlm := Eval.varRef_inv hs
  have hlk := Eval.varRef_inv hk
  simp [lgtm_env, CommentManager.get] at hlm hlk
  subst hlm
  subst hlk
  simp [CommentManager.get?, Value.lookupField?, Value.field?, hf, hlookup]

/-- The dual of `CommentManager.get.eq_get?`: a comment the manager holds under `ref` is what a call
to `CommentManager.get` on `ref` evaluates to.  Where that lemma drops the `ArgsHaveType` premise as
every inversion principle here does, this one has to produce it — a call it builds rather than takes
apart needs its arguments to fit — which is the one way this needs more than `get?`'s equation: a
typing fact about `manager` and about `ref` themselves, had wherever this is used from the thread
and manager invariants already in hand.

No extra comparability side condition appears: `CommentManager.get?` is `Value.lookupField?`, which
is `(KeyValues.lookup? kvs k).join`, so `get? manager ref = some c` already forces
`KeyValues.lookup? kvs k = some (some c)` — exactly what `Eval.EHashmapGet`'s third premise wants. -/
theorem CommentManager.get.apply_of_get? {td : TypeDecls} {gs : Globals} {manager ref c : Value}
    (hmanager : manager.HasType td (.struct "CommentManager"))
    (href : ref.HasType td (.struct "CommentRef"))
    (h : CommentManager.get? manager ref = some c) :
    CommentManager.get.Apply td gs [manager, ref] (.option (some c)) := by
  obtain ⟨fvs, rfl⟩ := Value.eq_struct_of_hasType hmanager
  obtain ⟨kvs, hkvs, hlookup⟩ : ∃ kvs, fvs.lookup "comments" = some (.hashmap kvs) ∧
      KeyValues.lookup? kvs ref = some (some c) := by
    simp only [CommentManager.get?, Value.lookupField?, Value.field?] at h
    cases hfc : fvs.lookup "comments" with
    | none => simp [hfc] at h
    | some w =>
      cases w with
      | hashmap kvs => exact ⟨kvs, by simp, by simpa [hfc, Option.join_eq_some_iff] using h⟩
      | _ => simp [hfc] at h
  refine .EApply _ (.cons "manager" hmanager (.cons "ref" href .nil)) ?_
  have hm : Eval td ((CommentManager.get).callEnv gs [.struct "CommentManager" fvs, ref])
      (.varRef "manager") (.struct "CommentManager" fvs) :=
    Eval.EVarRef _ (by simp [lgtm_env, CommentManager.get])
  have hk : Eval td ((CommentManager.get).callEnv gs [.struct "CommentManager" fvs, ref])
      (.varRef "ref") ref :=
    Eval.EVarRef _ (by simp [lgtm_env, CommentManager.get])
  exact Eval.EHashmapGet _ _ (Eval.EStructGet _ _ hm hkvs) hk hlookup

end
