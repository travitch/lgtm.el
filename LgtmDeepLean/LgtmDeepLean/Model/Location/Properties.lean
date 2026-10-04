module

public import LgtmDeepLean.Model.Location.Operations
meta import LgtmDeepLean.Model.Location.Operations

@[expose] public section

def CommentLocation.topLevelValue : Value := .ind "CommentLocation" "TopLevel" []

def ThreadLocation.topLevelValue : Value := .ind "ThreadLocation" "TopLevel" []

/-- `asThreadLocation` called on `TopLevel` returns `TopLevel`.

For every `td` and `gs`: a match resolves its alternative by the constructor the value carries, so
nothing on the way to this answer consults either table. -/
theorem CommentLocation.asThreadLocation.topLevel {td : TypeDecls} {gs : Globals} {tl : Value}
    (h : CommentLocation.asThreadLocation.Apply td gs [CommentLocation.topLevelValue] tl) :
    tl = ThreadLocation.topLevelValue := by
  obtain ⟨-, -, hbody⟩ := h
  cases hbody with
  | EIndMatch _ _ hs halt hb =>
    cases hs with
    | EVarRef _ hls =>
      simp [CommentLocation.asThreadLocation, CommentLocation.topLevelValue, FuncDecl.callEnv,
        Env.extend, Globals.env, Env.lookup] at hls
      obtain ⟨rfl, rfl, rfl⟩ := hls
      simp [List.lookup] at halt
      obtain ⟨rfl, rfl⟩ := halt
      cases hb with
      | EIndNew _ _ _ hlen _ =>
          simp [ThreadLocation.topLevelValue, List.eq_nil_of_length_eq_zero hlen.symm]

theorem ThreadLocation.isTopLevel.topLevel {td : TypeDecls} {gs : Globals} {res : Value}
    (h : ThreadLocation.isTopLevel.Apply td gs [ThreadLocation.topLevelValue] res) :
    res = .bool true := by
  obtain ⟨-, -, hbody⟩ := h
  cases hbody with
  | EIndMatch _ _ hs halt hb =>
    cases hs with
    | EVarRef _ hls =>
      simp [ThreadLocation.isTopLevel, ThreadLocation.topLevelValue, FuncDecl.callEnv, Env.extend,
        Globals.env, Env.lookup] at hls
      obtain ⟨rfl, rfl, rfl⟩ := hls
      simp [List.lookup] at halt
      obtain ⟨rfl, rfl⟩ := halt
      cases hb with
      | EBoolLit _ => rfl

/-- Converting a top-level comment location to a thread location leaves a top-level thread location. -/
theorem CommentLocation.topLevel_asThreadLocation_isTopLevel {td : TypeDecls} {gs : Globals}
    {tl res : Value}
    (htl : CommentLocation.asThreadLocation.Apply td gs [CommentLocation.topLevelValue] tl)
    (hres : ThreadLocation.isTopLevel.Apply td gs [tl] res) : res = .bool true :=
  ThreadLocation.isTopLevel.topLevel (CommentLocation.asThreadLocation.topLevel htl ▸ hres)

def locationTypes : TypeDecls :=
  { ss := Structs.ofDecls [CommentFileLocation]
    is := Inductives.ofDecls [ThreadLocation, CommentLocation] }

#guard CommentLocation.asThreadLocation.check locationTypes []
#guard ThreadLocation.isTopLevel.check locationTypes []

/-- A `TopLevel` carrying nothing has the type of whichever declaration in `locationTypes` declares
that constructor — which is both of them: the constructor is one the declaration has, and there is
nothing carried to hold to a type. -/
theorem hasType_topLevel {name : String} {d : InductiveDecl}
    (hd : locationTypes.is.lookup name = some d) (hc : d.constructors.lookup "TopLevel" = some []) :
    Value.HasType locationTypes (.ind name "TopLevel" []) (.ind name) :=
  .ind hd hc rfl (by simp)

theorem eval_asThreadLocation_topLevel :
    CommentLocation.asThreadLocation.Apply locationTypes [] [CommentLocation.topLevelValue]
      ThreadLocation.topLevelValue :=
  .EApply _ (.cons "loc" (hasType_topLevel rfl rfl) .nil)
    (.EIndMatch _ _ (.EVarRef "loc" rfl) rfl (.EIndNew (vs := []) _ _ _ rfl (by simp)))

theorem eval_isTopLevel_topLevel :
    ThreadLocation.isTopLevel.Apply locationTypes [] [ThreadLocation.topLevelValue] (.bool true) :=
  .EApply _ (.cons "l" (hasType_topLevel rfl rfl) .nil)
    (.EIndMatch _ _ (.EVarRef "l" rfl) rfl (.EBoolLit true))

/-- The premises met together: there is a thread location the conversion returns for `TopLevel`, and
asking `isTopLevel` of it returns `true`. -/
theorem exists_topLevel_asThreadLocation_isTopLevel :
    ∃ tl, CommentLocation.asThreadLocation.Apply locationTypes [] [CommentLocation.topLevelValue] tl
      ∧ ThreadLocation.isTopLevel.Apply locationTypes [] [tl] (.bool true) :=
  ⟨_, eval_asThreadLocation_topLevel, eval_isTopLevel_topLevel⟩

end
