module

public import LgtmDeepLean.Model.Location.Operations
meta import LgtmDeepLean.Model.Location.Operations

/-! # What the location functions return

The facts about the declarations in `LgtmDeepLean.Model.Location.Operations`: what the relational
semantics says each of them returns for a top-level location, and the values those answers are
stated in terms of.

Apart from the declarations themselves because the two are read for different reasons — the
declarations are the model, which `modelProgram` collects and extraction reads, and these are facts
a proof elsewhere needs about it.  The facts are for callers elsewhere to read too, so, as in
`Model.Basic`, this module hands out and exposes everything it declares. -/
@[expose] public section

/-- The value `CommentLocation`'s `TopLevel` builds, which is what the shallow model writes as
`CommentLocation.topLevel`.  A constructor that carries nothing carries an empty list. -/
def CommentLocation.topLevelValue : Value := .ind "CommentLocation" "TopLevel" []

/-- `ThreadLocation`'s own `TopLevel`, which is what the conversion produces for it. -/
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
      -- `TopLevel` carries no arguments, so the values the constructor was given are the empty list.
      | EIndNew _ _ _ hlen _ =>
          simp [ThreadLocation.topLevelValue, List.eq_nil_of_length_eq_zero hlen.symm]

/-- `isTopLevel` called on `TopLevel` returns `true`, which is the alternative that constructor
selects. -/
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

/-- Converting a top-level comment location to a thread location leaves a top-level thread location.

The shallow model states this as the two calls composed being `true`, proved by `rfl`.  Here a call is
a relation rather than a function and no declaration of the model composes these two, so the calls
become the premises and what they produce becomes the conclusion: whatever `asThreadLocation` returns
for `TopLevel`, asking `isTopLevel` of that returns `true`.

Which is also the shape a caller needs.  The shallow lemma exists because a caller in another module
cannot unfold either `def` to see the fact; a caller here holds two calls it cannot reduce either, and
this is what reduces them.

Not `@[simp]`, unlike the shallow lemma: the left-hand side of the conclusion is a variable, so there
is nothing for `simp` to match on.  `td` and `gs` are left open because neither call reads them. -/
theorem CommentLocation.topLevel_asThreadLocation_isTopLevel {td : TypeDecls} {gs : Globals}
    {tl res : Value}
    (htl : CommentLocation.asThreadLocation.Apply td gs [CommentLocation.topLevelValue] tl)
    (hres : ThreadLocation.isTopLevel.Apply td gs [tl] res) : res = .bool true :=
  ThreadLocation.isTopLevel.topLevel (CommentLocation.asThreadLocation.topLevel htl ▸ hres)

/-! ## The calls above are calls the model can make

Both premises of `topLevel_asThreadLocation_isTopLevel` are relations, so they would be as provable
of a declaration nothing can call as of one anything can: what follows is the two calls carried out,
which is what says the theorem is about something.

`locationTypes` is the table those two declarations need — the two inductive types they mention, and
the structure type `FileLocation` carries, which is what `asThreadLocation`'s *other* alternative
reads a field of.  It is not a table for the model as a whole; that belongs with the `Program` the
model will be read as. -/

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
