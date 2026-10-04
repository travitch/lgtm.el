module

public import LgtmDeepLean.Lang.IR
public import LgtmDeepLean.Lang.TypeCheck.Comparable
public import LgtmDeepLean.Lang.TypeCheck.TypeDecls

/-! # Inference

`Expression.infer` and the three walks it is mutual with, one per kind of list an expression holds,
with an inversion principle apiece: `infer`'s body is not visible outside this module, so those
lemmas are the whole of what a proof elsewhere can use.

What an expression is inferred under is here too — `Context`, the types of the variables in scope —
along with the two conditions inference states over lists rather than over any one subexpression:
`Ty.common`, which is what makes an `indMatch`'s alternatives agree on a type, and
`Expression.altsExhaustive`, which is what makes them one apiece for the constructors.  The facts
about `List.lookup` that the struct and match rules are read through are here with them, since it is
those rules that need them.

Checking an expression against an expected type is `Expression.check`, in
`LgtmDeepLean.Lang.TypeCheck`: every form determines its own type, so checking is this module plus a
comparison. -/

/-- The types of the variables in scope, innermost binding first. -/
public abbrev Context := List (String × Ty)

/-- A name is looked up in the left half of an appended context first, so what is on the left
shadows what is on the right. -/
public theorem Context.lookup_append {ctx₁ ctx₂ : Context} {x : String} :
    (ctx₁ ++ ctx₂).lookup x =
      match ctx₁.lookup x with
      | some t => some t
      | none => ctx₂.lookup x := by
  induction ctx₁ with
  | nil => rfl
  | cons p ps ih =>
      obtain ⟨k, t⟩ := p
      by_cases h : x == k <;> simp [List.lookup_cons, h, ih]

/-- If all of the given types are the same, return that type.  Otherwise `none`.

This is used to validate that all of the branches of an `indMatch` have the same type.  If the list
is empty, also return `none`. -/
public def Ty.common : List Ty → Option Ty
  | [] => none
  | t :: ts => if ts.all (· == t) then some t else none

/-- `Ty.common` satisfies its documented behavior. -/
@[simp, grind =] public theorem Ty.common_eq_some {ts : List Ty} {t : Ty} :
    Ty.common ts = some t ↔ ts ≠ [] ∧ ∀ t' ∈ ts, t' = t := by
  cases ts with
  | nil => simp [Ty.common]
  | cons t₀ ts =>
      constructor
      · intro h
        simp only [Ty.common] at h
        split at h
        · next hall =>
            obtain rfl : t₀ = t := Option.some.inj h
            refine ⟨by simp, fun t' ht' => ?_⟩
            rcases List.mem_cons.mp ht' with rfl | ht'
            · rfl
            · simpa using List.all_eq_true.mp hall t' ht'
        · simp at h
      · rintro ⟨-, hall⟩
        obtain rfl : t₀ = t := hall t₀ (by simp)
        have hcond : (ts.all (· == t₀)) = true :=
          List.all_eq_true.mpr fun t' ht' => by simp [hall t' (List.mem_cons_of_mem _ ht')]
        simp [Ty.common, hcond]

/-! Two facts about `List.lookup` over a pair of association lists carrying the same keys in the
same order.  Every rule about a struct is stated with `lookup`, and these are what carry a fact
about one such list over to another: the field types a declaration gives, the expressions a
`structNew` gives for them, and the values those evaluate to are three lists with one key sequence
between them. -/

/-- Association lists with the same keys in the same order are defined at the same names. -/
public theorem List.lookup_isSome_congr {α β γ : Type} [BEq α] {as : List (α × β)}
    {bs : List (α × γ)} (h : as.map Prod.fst = bs.map Prod.fst) (k : α) :
    (as.lookup k).isSome = (bs.lookup k).isSome := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all
  | cons p as ih =>
      cases bs with
      | nil => simp at h
      | cons q bs =>
          obtain ⟨ka, a⟩ := p
          obtain ⟨kb, b⟩ := q
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨rfl, h⟩ := h
          by_cases hk : k == ka <;> simp [List.lookup_cons, hk, ih h]

/-- A lookup succeeds exactly for the names the list carries.

`List.lookup_isSome_congr` compares two association lists with each other; this compares one with its
own keys, which is what a fact stated over `List.Perm` — as `Expression.altsExhaustive` is — has to
be read through: a permutation says which names are there, and this is what that means for looking
one up. -/
private theorem List.lookup_isSome_iff_mem_keys {α β : Type} [BEq α] [LawfulBEq α]
    {l : List (α × β)} {k : α} : (l.lookup k).isSome ↔ k ∈ l.map Prod.fst := by
  simp only [List.lookup_isSome_iff, List.mem_map]
  grind

/-- Where two such lists both resolve a name, the entries they resolve it to are paired in the zip.

This is what turns a premise stated over `List.zip` — as `Eval`'s rules for the struct forms are,
following `EApp` — into one about the entry a `lookup` found. -/
public theorem List.mem_zip_of_lookup {α β γ : Type} [BEq α] [LawfulBEq α] {as : List (α × β)}
    {bs : List (α × γ)} {k : α} {b : β} {c : γ} (h : as.map Prod.fst = bs.map Prod.fst)
    (hb : as.lookup k = some b) (hc : bs.lookup k = some c) : ((k, b), (k, c)) ∈ as.zip bs := by
  induction as generalizing bs with
  | nil => simp at hb
  | cons p as ih =>
      cases bs with
      | nil => simp at h
      | cons q bs =>
          obtain ⟨ka, a⟩ := p
          obtain ⟨kb, b'⟩ := q
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨rfl, h⟩ := h
          rw [List.lookup_cons] at hb hc
          by_cases hk : k == ka
          · obtain rfl : k = ka := by grind
            simp only [hk] at hb hc
            simp_all
          · simp only [hk] at hb hc
            exact List.mem_cons_of_mem _ (ih h hb hc)

/-- A lookup only ever hands back an entry the list contains, which is how a fact stated over every
entry of a table — as `Globals.WellTyped` and `structUpdate`'s typing rule both are — reaches the one
entry a name resolved to. -/
public theorem List.mem_of_lookup {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {k : α}
    {b : β} (h : l.lookup k = some b) : (k, b) ∈ l := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
      obtain ⟨k', b'⟩ := p
      rw [List.lookup_cons] at h
      split at h
      · obtain rfl : k = k' := by grind
        obtain rfl : b = b' := by grind
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)

/-! ## Exhaustiveness

What a match's alternatives have to be, as a condition on the two lists rather than on any one
alternative.  It is separate from `Expression.inferAlts` because it is not something the walk along
the alternatives can see: each alternative resolves its own constructor by name, and no alternative
knows whether the others between them covered the rest. -/

/-- The alternatives of a match expression must be exhaustive.

This is checked by validating that the constructor names of the cases are a permutation of
the constructor names in the inductive declaration. -/
@[expose] public def Expression.altsExhaustive (cs : List (CtorName × List Ty))
    (alts : List (CtorName × List String × Expression)) : Bool :=
  (alts.map Prod.fst).isPerm (cs.map Prod.fst)

/-- `Expression.altsExhaustive` is correct. -/
public theorem Expression.altsExhaustive_eq_true {cs : List (CtorName × List Ty)}
    {alts : List (CtorName × List String × Expression)} :
    Expression.altsExhaustive cs alts = true ↔ (alts.map Prod.fst).Perm (cs.map Prod.fst) := by
  simp [Expression.altsExhaustive, List.isPerm_iff]

/-- Every constructor of the declaration has an alternative (a derived fact from exhaustiveness).

This is stated over `lookup` because that is how both lists are read in `Eval.EIndMatch` and
`Value.HasType`. -/
public theorem Expression.lookup_isSome_of_altsExhaustive {cs : List (CtorName × List Ty)}
    {alts : List (CtorName × List String × Expression)}
    (h : Expression.altsExhaustive cs alts = true) {c : CtorName} (hc : (cs.lookup c).isSome) :
    (alts.lookup c).isSome :=
  List.lookup_isSome_iff_mem_keys.mpr
    ((Expression.altsExhaustive_eq_true.mp h).mem_iff.mpr (List.lookup_isSome_iff_mem_keys.mp hc))

/-- Over a declaration that names each of its constructors once, an exhaustive match names each of
its alternatives' constructors once too. -/
public theorem Expression.alts_nodup_of_altsExhaustive {cs : List (CtorName × List Ty)}
    {alts : List (CtorName × List String × Expression)} (hu : (cs.map Prod.fst).Nodup)
    (h : Expression.altsExhaustive cs alts = true) : (alts.map Prod.fst).Nodup :=
  (Expression.altsExhaustive_eq_true.mp h).nodup_iff.mpr hu

mutual

/-- Infer the type of `e` under `ctx`, or `none` if `e` is ill typed. -/
public def Expression.infer (td : TypeDecls) (ctx : Context) : Expression → Option Ty
  | .lam ps body => do
    let r ← body.infer td (ps ++ ctx)
    some (.fn (ps.map Prod.snd) r)
  | .app f args =>
    match f.infer td ctx with
    | some (.fn ps r) => if Expression.inferList td ctx args == some ps then some r else none
    | _ => none
  | .boolLit _ => some .bool
  | .ite c thn els => do
    guard (c.infer td ctx == some .bool)
    let t ← thn.infer td ctx
    guard (els.infer td ctx == some t)
    some t
  | .equals l r => do
    let t ← l.infer td ctx
    guard (r.infer td ctx == some t)
    guard (Ty.comparable td t)
    some .bool
  | .let_ x e body => do
    let t ← e.infer td ctx
    body.infer td ((x, t) :: ctx)
  | .varRef x => ctx.lookup x
  | .structNew name fes =>
    match td.ss.lookup name with
    | some sd =>
      if Expression.inferFields td ctx fes == some sd.fields then some (.struct name) else none
    | none => none
  | .structGet e f =>
    match e.infer td ctx with
    | some (.struct name) =>
      match td.ss.lookup name with
      | some sd => sd.fields.lookup f
      | none => none
    | _ => none
  | .structUpdate e fes =>
    match e.infer td ctx, Expression.inferFields td ctx fes with
    | some (.struct name), some fts =>
      match td.ss.lookup name with
      | some sd =>
        if !fts.isEmpty && fts.all fun p => sd.fields.lookup p.1 == some p.2 then
          some (.struct name)
        else none
      | none => none
    | _, _ => none
  | .indNew name c args => do
    let d ← td.is.lookup name
    let ts ← d.constructors.lookup c
    guard (Expression.inferList td ctx args == some ts)
    some (.ind name)
  | .indMatch scrut alts =>
    match scrut.infer td ctx with
    | some (.ind name) => do
      let d ← td.is.lookup name
      guard (Expression.altsExhaustive d.constructors alts)
      let rs ← Expression.inferAlts td ctx d.constructors alts
      Ty.common rs
    | _ => none
  | .intLit _ => some .int
  | .plus l r | .minus l r =>
    if l.infer td ctx == some .int && r.infer td ctx == some .int then some .int else none
  | .stringLit _ => some .string
  | .lnil t => some (.list t)
  | .lcons hd tl => do
    let t ← hd.infer td ctx
    guard (tl.infer td ctx == some (.list t))
    some (.list t)
  | .listReverse l =>
    match l.infer td ctx with
    | some (.list t) => some (.list t)
    | _ => none

/-- Infer the types of `es`, in order, or `none` if any one of them is ill typed. -/
public def Expression.inferList (td : TypeDecls) (ctx : Context) :
    List Expression → Option (List Ty)
  | [] => some []
  | e :: es => do
    let t ← e.infer td ctx
    let ts ← Expression.inferList td ctx es
    some (t :: ts)

/-- Infer the type of each field's expression, keeping the field it belongs to, or `none` if any one
of them is ill typed.

The result is an association list of the fields given, in the order given, which is what lets
`structNew` compare it against a declaration's field list in one step.  `structUpdate`, which names
only some of the fields, reads it with `lookup` instead. -/
public def Expression.inferFields (td : TypeDecls) (ctx : Context) :
    List (FieldName × Expression) → Option (List (FieldName × Ty))
  | [] => some []
  | (f, e) :: fes => do
    let t ← e.infer td ctx
    let fts ← Expression.inferFields td ctx fes
    some ((f, t) :: fts)

/-- Infer the type of each alternative's expression, in the order the alternatives were written, or
`none` if one of them is for a constructor `cs` does not declare, binds the wrong number of names, or
has an ill-typed expression. -/
public def Expression.inferAlts (td : TypeDecls) (ctx : Context) (cs : List (CtorName × List Ty)) :
    List (CtorName × List String × Expression) → Option (List Ty)
  | [] => some []
  | (c, xs, body) :: alts => do
    let ts ← cs.lookup c
    guard (xs.length == ts.length)
    let t ← body.infer td (xs.zip ts ++ ctx)
    let rs ← Expression.inferAlts td ctx cs alts
    some (t :: rs)

end

/-! Inversion principles for `infer`, one per syntactic form.

`infer`'s body is not visible outside this module, so a proof elsewhere cannot unfold it and has
to go through these instead.  They are `simp` lemmas, so a hypothesis `e.infer td ctx = some t`
decomposes into premises about `e`'s subterms automatically. -/

@[simp, grind =] public theorem Expression.infer_varRef {td : TypeDecls} {ctx : Context}
    {x : String} :
    (Expression.varRef x).infer td ctx = ctx.lookup x := by
  simp [Expression.infer]

@[simp, grind =] public theorem Expression.infer_boolLit {td : TypeDecls} {ctx : Context}
    {b : Bool} :
    (Expression.boolLit b).infer td ctx = some .bool := by
  simp [Expression.infer]

@[simp, grind =] public theorem Expression.infer_intLit {td : TypeDecls} {ctx : Context} {i : Int} :
    (Expression.intLit i).infer td ctx = some .int := by
  simp [Expression.infer]

@[simp, grind =] public theorem Expression.infer_stringLit {td : TypeDecls} {ctx : Context}
    {s : String} :
    (Expression.stringLit s).infer td ctx = some .string := by
  simp [Expression.infer]

@[simp, grind =] public theorem Expression.infer_lnil {td : TypeDecls} {ctx : Context} {t : Ty} :
    (Expression.lnil t).infer td ctx = some (.list t) := by
  simp [Expression.infer]

/-- A `plus` is typeable exactly when both operands are `int`s, and then it is an `int`. -/
@[simp, grind =] public theorem Expression.infer_plus_eq_some {td : TypeDecls} {ctx : Context}
    {l r : Expression} {t : Ty} :
    (Expression.plus l r).infer td ctx = some t ↔
      l.infer td ctx = some .int ∧ r.infer td ctx = some .int ∧ t = .int := by
  simp [Expression.infer]
  grind

/-- A `minus` is typeable exactly when both operands are `int`s, and then it is an `int`. -/
@[simp, grind =] public theorem Expression.infer_minus_eq_some {td : TypeDecls} {ctx : Context}
    {l r : Expression} {t : Ty} :
    (Expression.minus l r).infer td ctx = some t ↔
      l.infer td ctx = some .int ∧ r.infer td ctx = some .int ∧ t = .int := by
  simp [Expression.infer]
  grind

/-- An `lcons` is typeable exactly when its tail is a list of its head's type.

This is what makes the values `Eval` builds homogeneous: the element type is read off the head
and then *required* of the tail, so one `Ty` covers every element. -/
@[simp, grind =] public theorem Expression.infer_lcons_eq_some {td : TypeDecls} {ctx : Context}
    {hd tl : Expression} {t : Ty} :
    (Expression.lcons hd tl).infer td ctx = some t ↔
      ∃ t', hd.infer td ctx = some t' ∧ tl.infer td ctx = some (.list t') ∧ t = .list t' := by
  simp [Expression.infer, Option.bind_eq_some_iff, guard]
  grind

/-- A `listReverse` is typeable when its operand is a list, and then it has that same list
type.

Reversing preserves both the length and the element type, so the operand's type is also the
result's: unlike `lcons`, this form introduces no new type structure. -/
@[simp, grind =] public theorem Expression.infer_listReverse_eq_some {td : TypeDecls}
    {ctx : Context} {l : Expression} {t : Ty} :
    (Expression.listReverse l).infer td ctx = some t ↔
      ∃ t', l.infer td ctx = some (.list t') ∧ t = .list t' := by
  simp only [Expression.infer]
  split <;> grind

/-- A `lam` is typeable when its body is, under its parameters extended with the enclosing
context, and then it is a function from the parameters' types to the body's.

Parameters go on the front of the context, so they shadow same-named bindings from outside, and — as
in `FuncDecl.callEnv` — a name repeated in the parameter list refers to its leftmost occurrence. -/
@[simp, grind =] public theorem Expression.infer_lam_eq_some {td : TypeDecls} {ctx : Context}
    {ps : List (String × Ty)} {body : Expression} {t : Ty} :
    (Expression.lam ps body).infer td ctx = some t ↔
      ∃ r, body.infer td (ps ++ ctx) = some r ∧ t = .fn (ps.map Prod.snd) r := by
  simp [Expression.infer, Option.bind_eq_some_iff]
  grind

/-- An `app` is typeable when its function's type is a function type whose parameter types
are the types of the arguments, in order, and then it is that function type's result.

Because `Ty.fn` records all the parameters at once, arity is part of that one comparison: a call
passing too few arguments is ill typed rather than partially applied. -/
@[simp, grind =] public theorem Expression.infer_app_eq_some {td : TypeDecls} {ctx : Context}
    {f : Expression} {args : List Expression} {t : Ty} :
    (Expression.app f args).infer td ctx = some t ↔
      ∃ ps, f.infer td ctx = some (.fn ps t) ∧ Expression.inferList td ctx args = some ps := by
  simp only [Expression.infer]
  split <;> grind

/-- An `ite` is typeable when its condition is a `bool` and its two branches have one type —
and then that is its type. -/
@[simp, grind =] public theorem Expression.infer_ite_eq_some {td : TypeDecls} {ctx : Context}
    {c thn els : Expression} {t : Ty} :
    (Expression.ite c thn els).infer td ctx = some t ↔
      c.infer td ctx = some .bool ∧ thn.infer td ctx = some t ∧ els.infer td ctx = some t := by
  simp [Expression.infer, Option.bind_eq_some_iff, guard]

/-- An `equals` is typeable when its two operands are the same type and that type is one a
comparison can reach the bottom of (see `Ty.comparable`).  The `equals` itself is of type `bool`. -/
@[simp, grind =] public theorem Expression.infer_equals_eq_some {td : TypeDecls} {ctx : Context}
    {l r : Expression} {t : Ty} :
    (Expression.equals l r).infer td ctx = some t ↔
      ∃ t', l.infer td ctx = some t' ∧ r.infer td ctx = some t' ∧ Ty.comparable td t' = true
        ∧ t = .bool := by
  simp [Expression.infer, Option.bind_eq_some_iff, guard]
  grind

/-- A `let_` is typeable when the expression it binds is and its body is under that name at
that type, and then it has the body's type. -/
@[simp, grind =] public theorem Expression.infer_let_eq_some {td : TypeDecls} {ctx : Context}
    {x : String} {e body : Expression} {t : Ty} :
    (Expression.let_ x e body).infer td ctx = some t ↔
      ∃ t', e.infer td ctx = some t' ∧ body.infer td ((x, t') :: ctx) = some t := by
  simp [Expression.infer, Option.bind_eq_some_iff]

/-- A `structNew` is typeable when the name it gives is declared and the fields it gives are
that declaration's fields, in that order, at those types. -/
@[simp, grind =] public theorem Expression.infer_structNew_eq_some {td : TypeDecls} {ctx : Context}
    {name : String} {fes : List (FieldName × Expression)} {t : Ty} :
    (Expression.structNew name fes).infer td ctx = some t ↔
      ∃ sd, td.ss.lookup name = some sd ∧ Expression.inferFields td ctx fes = some sd.fields
        ∧ t = .struct name := by
  simp only [Expression.infer]
  split <;> grind

/-- A `structGet` is typeable when its operand is a declared struct with the named field. -/
@[simp, grind =] public theorem Expression.infer_structGet_eq_some {td : TypeDecls} {ctx : Context}
    {e : Expression} {f : FieldName} {t : Ty} :
    (Expression.structGet e f).infer td ctx = some t ↔
      ∃ name sd, e.infer td ctx = some (.struct name) ∧ td.ss.lookup name = some sd
        ∧ sd.fields.lookup f = some t := by
  simp only [Expression.infer]
  split <;> grind

/-- A `structUpdate` is typeable when its operand is a declared struct and every field it
rebinds is one of that declaration's, at the type the declaration gives it. -/
@[simp, grind =] public theorem Expression.infer_structUpdate_eq_some {td : TypeDecls}
    {ctx : Context} {e : Expression} {fes : List (FieldName × Expression)} {t : Ty} :
    (Expression.structUpdate e fes).infer td ctx = some t ↔
      ∃ name sd fts, e.infer td ctx = some (.struct name) ∧ td.ss.lookup name = some sd
        ∧ Expression.inferFields td ctx fes = some fts ∧ fts ≠ []
        ∧ (∀ p ∈ fts, sd.fields.lookup p.1 = some p.2) ∧ t = .struct name := by
  simp only [Expression.infer]
  split <;> grind

/-- An `indNew` is typeable when the type it names is declared, that declaration has the
constructor it names, and the arguments are the data types that constructor takes, in order. -/
@[simp, grind =] public theorem Expression.infer_indNew_eq_some {td : TypeDecls} {ctx : Context}
    {name : String} {c : CtorName} {args : List Expression} {t : Ty} :
    (Expression.indNew name c args).infer td ctx = some t ↔
      ∃ d ts, td.is.lookup name = some d ∧ d.constructors.lookup c = some ts
        ∧ Expression.inferList td ctx args = some ts ∧ t = .ind name := by
  simp [Expression.infer, Option.bind_eq_some_iff, guard]
  grind

/-- An `indMatch` is typeable when its scrutinee is a declared inductive type, it has one
alternative per constructor of that declaration, those alternatives all check, and they all have one
type. -/
@[simp, grind =] public theorem Expression.infer_indMatch_eq_some {td : TypeDecls} {ctx : Context}
    {scrut : Expression} {alts : List (CtorName × List String × Expression)} {t : Ty} :
    (Expression.indMatch scrut alts).infer td ctx = some t ↔
      ∃ name d rs, scrut.infer td ctx = some (.ind name) ∧ td.is.lookup name = some d
        ∧ Expression.altsExhaustive d.constructors alts = true
        ∧ Expression.inferAlts td ctx d.constructors alts = some rs ∧ rs ≠ []
        ∧ ∀ t' ∈ rs, t' = t := by
  simp only [Expression.infer]
  split <;> simp_all [Option.bind_eq_some_iff, guard]

/-! Inversion principles for `inferList`.  Together these say what it computes: the argument types
in order, and `none` as soon as one argument has no type. -/

@[simp, grind =] public theorem Expression.inferList_nil {td : TypeDecls} {ctx : Context} :
    Expression.inferList td ctx [] = some [] := by
  simp [Expression.inferList]

@[simp, grind =] public theorem Expression.inferList_cons_eq_some {td : TypeDecls} {ctx : Context}
    {e : Expression} {es : List Expression} {ts : List Ty} :
    Expression.inferList td ctx (e :: es) = some ts ↔
      ∃ t ts', e.infer td ctx = some t ∧ Expression.inferList td ctx es = some ts'
        ∧ ts = t :: ts' := by
  simp [Expression.inferList, Option.bind_eq_some_iff]
  grind

/-! Inversion principles for `inferFields`, and then what it says about the list it produces: the
fields it was given, in order, and `none` as soon as one field's expression has no type. -/

@[simp, grind =] public theorem Expression.inferFields_nil {td : TypeDecls} {ctx : Context} :
    Expression.inferFields td ctx [] = some [] := by
  simp [Expression.inferFields]

@[simp, grind =] public theorem Expression.inferFields_cons_eq_some {td : TypeDecls} {ctx : Context}
    {f : FieldName} {e : Expression} {fes : List (FieldName × Expression)}
    {fts : List (FieldName × Ty)} :
    Expression.inferFields td ctx ((f, e) :: fes) = some fts ↔
      ∃ t fts', e.infer td ctx = some t ∧ Expression.inferFields td ctx fes = some fts'
        ∧ fts = (f, t) :: fts' := by
  simp [Expression.inferFields, Option.bind_eq_some_iff]
  grind

/-- Inference renames nothing: the fields it reports are the fields it was given, in that order.

This is the fact that ties the three lists a `structNew` involves together.  Its declaration's fields
are `inferFields`' output, the expressions are its input, and `Eval` relates those to the values, so
one key sequence runs through all four. -/
public theorem Expression.map_fst_of_inferFields {td : TypeDecls} {ctx : Context}
    {fes : List (FieldName × Expression)} {fts : List (FieldName × Ty)}
    (h : Expression.inferFields td ctx fes = some fts) :
    fts.map Prod.fst = fes.map Prod.fst := by
  induction fes generalizing fts with
  | nil => simp_all
  | cons p fes ih =>
      obtain ⟨f, e⟩ := p
      obtain ⟨t, fts', -, hfts, rfl⟩ := Expression.inferFields_cons_eq_some.mp h
      simp [ih hfts]

/-- The type `inferFields` reports for a field is the type of the expression that field was given.

Stated over `lookup` rather than position because that is how both struct rules read the list: a
field's expression is found by name, and the type beside it is the one that field has. -/
public theorem Expression.lookup_of_inferFields {td : TypeDecls} {ctx : Context}
    {fes : List (FieldName × Expression)} {fts : List (FieldName × Ty)}
    (h : Expression.inferFields td ctx fes = some fts) {f : FieldName} {e : Expression}
    (hf : fes.lookup f = some e) : ∃ t, fts.lookup f = some t ∧ e.infer td ctx = some t := by
  induction fes generalizing fts with
  | nil => simp at hf
  | cons p fes ih =>
      obtain ⟨g, e'⟩ := p
      obtain ⟨t, fts', he', hfts, rfl⟩ := Expression.inferFields_cons_eq_some.mp h
      rw [List.lookup_cons] at hf ⊢
      split at hf
      · exact ⟨t, by simp_all, by grind⟩
      · exact ih hfts hf

/-! Inversion principles for `inferAlts`.  There is one alternative list to run out, and the second
says what one step along it asks for. -/

@[simp, grind =] public theorem Expression.inferAlts_nil {td : TypeDecls} {ctx : Context}
    {cs : List (CtorName × List Ty)} : Expression.inferAlts td ctx cs [] = some [] := by
  simp [Expression.inferAlts]

/-- One step of the walk: the alternative is for a constructor the declaration has, it binds one
name per data type that constructor carries, and its expression is typeable under those names at
those types. -/
@[simp, grind =] public theorem Expression.inferAlts_cons_eq_some {td : TypeDecls} {ctx : Context}
    {cs : List (CtorName × List Ty)} {c : CtorName} {xs : List String} {body : Expression}
    {alts : List (CtorName × List String × Expression)} {rs : List Ty} :
    Expression.inferAlts td ctx cs ((c, xs, body) :: alts) = some rs ↔
      ∃ ts t rs', cs.lookup c = some ts ∧ xs.length = ts.length
        ∧ body.infer td (xs.zip ts ++ ctx) = some t
        ∧ Expression.inferAlts td ctx cs alts = some rs' ∧ rs = t :: rs' := by
  simp [Expression.inferAlts, Option.bind_eq_some_iff, guard]
  grind

/-- The alternative a constructor's name resolves to is the one checked against that constructor's
data types, and the type inferred for its expression is one of the types `inferAlts` reports. -/
public theorem Expression.lookup_of_inferAlts {td : TypeDecls} {ctx : Context}
    {cs : List (CtorName × List Ty)} {alts : List (CtorName × List String × Expression)}
    {rs : List Ty} (h : Expression.inferAlts td ctx cs alts = some rs) {c : CtorName}
    {ts : List Ty} {xs : List String} {body : Expression} (hc : cs.lookup c = some ts)
    (ha : alts.lookup c = some (xs, body)) :
    ∃ t, t ∈ rs ∧ xs.length = ts.length ∧ body.infer td (xs.zip ts ++ ctx) = some t := by
  induction alts generalizing rs with
  | nil => simp at ha
  | cons q alts ih =>
      obtain ⟨c₀, xs₀, body₀⟩ := q
      obtain ⟨ts₀, t₀, rs', hc₀, hlen, hbody, halts, rfl⟩ := Expression.inferAlts_cons_eq_some.mp h
      rw [List.lookup_cons] at ha
      by_cases hcc : c == c₀
      · obtain rfl : c = c₀ := by grind
        simp only [hcc] at ha
        obtain ⟨rfl, rfl⟩ : xs = xs₀ ∧ body = body₀ := by grind
        obtain rfl : ts = ts₀ := by grind
        exact ⟨t₀, by simp, hlen, hbody⟩
      · simp only [hcc] at ha
        obtain ⟨t, htmem, htlen, htbody⟩ := ih halts ha
        exact ⟨t, List.mem_cons_of_mem _ htmem, htlen, htbody⟩
