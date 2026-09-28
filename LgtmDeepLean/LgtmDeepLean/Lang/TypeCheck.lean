module

public import LgtmDeepLean.Lang.IR
meta import LgtmDeepLean.Lang.IR

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

/-! ## Structure declarations

The types a `Ty.struct` can name.  A `Structs` is to structure types what `Globals` is to
declarations: one table, keyed by the name each entry declares, that the whole program is checked
against.

Unlike `Globals` it never turns into a `Context`, and so it has to be threaded through
`Expression.infer` explicitly — as the `ss` field of the `TypeDecls` below, which is the parameter
inference actually takes.  A global can be folded into the context before inference starts —
its name is a variable, and `Globals.types` is the bindings it contributes — where a struct name is
not a variable at all.  Nothing mentions a struct type without also mentioning one of the three
struct forms, and each of those resolves its name here. -/

/-- The structure types in scope everywhere, each under the name it declares. -/
public abbrev Structs := List (String × StructDecl)

/-- Key each structure declaration by the name it declares. -/
@[expose] public def Structs.ofDecls (sds : List StructDecl) : Structs :=
  sds.map fun s => (s.name, s)

@[simp] public theorem Structs.ofDecls_nil : Structs.ofDecls [] = [] := by simp [Structs.ofDecls]

@[simp] public theorem Structs.ofDecls_cons (s : StructDecl) (sds : List StructDecl) :
    Structs.ofDecls (s :: sds) = (s.name, s) :: Structs.ofDecls sds := by simp [Structs.ofDecls]

/-! ## Inductive type declarations

The types a `Ty.ind` can name.  An `Inductives` is to inductive types exactly what `Structs` is to
structure types — one table, keyed by the name each entry declares — and it is threaded through
inference for the same reason: an inductive type's name is not a variable, so there is nothing for a
`Context` to say about it. -/

/-- The inductive types in scope everywhere, each under the name it declares. -/
public abbrev Inductives := List (String × InductiveDecl)

/-- Key each inductive declaration by the name it declares. -/
@[expose] public def Inductives.ofDecls (ids : List InductiveDecl) : Inductives :=
  ids.map fun d => (d.name, d)

@[simp] public theorem Inductives.ofDecls_nil : Inductives.ofDecls [] = [] := by
  simp [Inductives.ofDecls]

@[simp] public theorem Inductives.ofDecls_cons (d : InductiveDecl) (ids : List InductiveDecl) :
    Inductives.ofDecls (d :: ids) = (d.name, d) :: Inductives.ofDecls ids := by
  simp [Inductives.ofDecls]

/-- The one type every entry of `ts` is, or `none` if they differ or there are none of them.

This is what an `indMatch` has to be able to do with the types of its alternatives: the match has one
type, so they all have to be that one.  There is no expected type to fall back on for an empty list,
so `none` it is — which is what makes a match over a type with no constructors ill typed. -/
public def Ty.common : List Ty → Option Ty
  | [] => none
  | t :: ts => if ts.all (· == t) then some t else none

/-- `Ty.common` is what it says it is: a type they all are, and there is at least one of them. -/
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

/-! ## Type declarations

Every table a type name resolves in, bundled into one parameter.  There are two of them —
`Structs` and `Inductives` — and the bundle is what keeps them from being two parameters threaded
through `Expression.infer`, `Value.HasType`, `Eval`, and every rule stated over them: a further kind
of declaration adds a field here and nothing else changes shape.

Every field defaults to empty, so `{}` is the bundle that declares no types at all — the one a
program using none of them is checked against. -/

/-- The type declarations in scope everywhere: one bundle, threaded through everything that has a
type name to resolve. -/
public structure TypeDecls where
  /-- The structure types, each under the name it declares. -/
  ss : Structs := []
  /-- The inductive types, each under the name it declares. -/
  is : Inductives := []
  deriving Repr

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
public theorem List.lookup_isSome_iff_mem_keys {α β : Type} [BEq α] [LawfulBEq α]
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

/-- With no two entries sharing a key, every entry of an association list is the one its own key
resolves to.

The converse of `List.mem_of_lookup`, and the direction that needs the keys to be distinct: a
repeated key is resolved to its leftmost entry, so nothing further along is reachable at all.
`List.lookup_keyed_self` below is the same fact for a list keyed by a function, which is how a table
of declarations is built; this is for one that is already a list of pairs, which is what an
inductive declaration's constructors are. -/
public theorem List.lookup_of_mem {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)}
    (hu : (l.map Prod.fst).Nodup) {k : α} {b : β} (h : (k, b) ∈ l) : l.lookup k = some b := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
      obtain ⟨k', b'⟩ := p
      rw [List.map_cons, List.nodup_cons] at hu
      rcases List.mem_cons.mp h with heq | hmem
      · obtain ⟨rfl, rfl⟩ : k = k' ∧ b = b' := by grind
        simp
      · have hne : ¬ (k == k') = true := fun hk =>
          hu.1 (List.mem_map.mpr ⟨(k, b), hmem, by grind⟩)
        simpa [List.lookup_cons, hne] using ih hu.2 hmem

/-- Keying a list by a function that is injective on it resolves every element to itself.

`Globals.ofDecls` and `Structs.ofDecls` both build a table this way — from the declarations a program
is written as, keyed by the name each one declares — so this is the one fact both need: with no two
entries sharing a key, none of them is shadowed. -/
public theorem List.lookup_keyed_self {α β : Type} [BEq α] [LawfulBEq α] {f : β → α} {bs : List β}
    (hu : (bs.map f).Nodup) {b : β} (hb : b ∈ bs) :
    (bs.map fun x => (f x, x)).lookup (f b) = some b := by
  induction bs with
  | nil => simp at hb
  | cons c cs ih =>
      rw [List.map_cons, List.nodup_cons] at hu
      simp only [List.map_cons, List.lookup_cons]
      rcases List.mem_cons.mp hb with rfl | hb'
      · simp
      · have hne : ¬ (f b == f c) = true := fun h =>
          hu.1 (List.mem_map.mpr ⟨b, hb', by grind⟩)
        simpa [hne] using ih hu.2 hb'

/-! ## Exhaustiveness

What a match's alternatives have to be, as a condition on the two lists rather than on any one
alternative.  It is separate from `Expression.inferAlts` because it is not something the walk along
the alternatives can see: each alternative resolves its own constructor by name, and no alternative
knows whether the others between them covered the rest. -/

/-- The alternatives `alts` are one apiece for the constructors `cs`, in whatever order.

Alternatives are keyed by constructor name rather than positional, so what exhaustiveness asks for is
that the names they give and the names `cs` declares are the same names, as many of each — a
permutation, which is one comparison the way the lockstep walk this replaces was.  A constructor with
no alternative and an alternative for a constructor the declaration does not have each leave a name
on one side with nothing on the other to pair it with, and an alternative repeated leaves two.

The names are compared as a multiset rather than as a set because this is a condition on two lists
and nothing else: `InductiveDecl.CtorNamesUnique` is what says a declaration names each of its
constructors once, and the checker does not assume it.  For a declaration that has it the two come
to the same thing — `Expression.alts_nodup_of_altsExhaustive` is that step — and for one that does
not, asking for a permutation asks for exactly as many alternatives as there are entries, which is
the honest count even though `List.lookup` leaves all but the leftmost of them dead.

Only the names are compared here.  What an alternative does with what its constructor carries is
`Expression.inferAlts`' business, and that is where the constructor is resolved by name — which is
what lets the two lists disagree on order at all.

Exposed, unlike `Expression.infer` and the rest of the checker: it is one comparison on two lists a
concrete program writes out, so a proof that a declaration checks is left with this on a pair of
literals and has to be able to see through it. -/
@[expose] public def Expression.altsExhaustive (cs : List (CtorName × List Ty))
    (alts : List (CtorName × List String × Expression)) : Bool :=
  (alts.map Prod.fst).isPerm (cs.map Prod.fst)

/-- `Expression.altsExhaustive` is what it says it is: the alternatives' constructor names are the
declaration's constructor names, as many of each. -/
public theorem Expression.altsExhaustive_eq_true {cs : List (CtorName × List Ty)}
    {alts : List (CtorName × List String × Expression)} :
    Expression.altsExhaustive cs alts = true ↔ (alts.map Prod.fst).Perm (cs.map Prod.fst) := by
  simp [Expression.altsExhaustive, List.isPerm_iff]

/-- Every constructor of the declaration has an alternative, which is the fact exhaustiveness exists
to supply.

Stated over `lookup` because that is how both lists are read where it matters: `Eval`'s `EIndMatch`
finds its alternative by the constructor the value carries, and `Value.HasType` finds that
constructor in the declaration, so this is what says a match cannot be handed a value of its
scrutinee's type that it has no alternative for. -/
public theorem Expression.lookup_isSome_of_altsExhaustive {cs : List (CtorName × List Ty)}
    {alts : List (CtorName × List String × Expression)}
    (h : Expression.altsExhaustive cs alts = true) {c : CtorName} (hc : (cs.lookup c).isSome) :
    (alts.lookup c).isSome :=
  List.lookup_isSome_iff_mem_keys.mpr
    ((Expression.altsExhaustive_eq_true.mp h).mem_iff.mpr (List.lookup_isSome_iff_mem_keys.mp hc))

/-- Over a declaration that names each of its constructors once, an exhaustive match names each of
its alternatives' constructors once too.

Which is what says no alternative of such a match is dead: `Eval` finds an alternative by `lookup`,
so a repeated name would leave every alternative for it beyond the leftmost unreachable, and this
rules that out from the one condition `InductiveDecl.CtorNamesUnique` puts on the declaration.  The
permutation is what carries it across: two lists with the same names as many of each are `Nodup`
together. -/
public theorem Expression.alts_nodup_of_altsExhaustive {cs : List (CtorName × List Ty)}
    {alts : List (CtorName × List String × Expression)} (hu : (cs.map Prod.fst).Nodup)
    (h : Expression.altsExhaustive cs alts = true) : (alts.map Prod.fst).Nodup :=
  (Expression.altsExhaustive_eq_true.mp h).nodup_iff.mpr hu

mutual

/-- Infer the type of `e` under `ctx`, or `none` if `e` is ill typed.

Every form determines its own type: `lnil` carries the element type of the empty list it builds and
`lam` carries the types of its parameters, so inference never has to guess and needs no expected
type to work from.  `Expression.check` is therefore just this function plus a comparison.

`td` is the one thing inference needs that the context does not supply.  A struct type is a name, so
each of the three struct forms has to resolve it in `td.ss`: `structNew` to find the fields it must
initialize, `structGet` to find the type of the field it reads, and `structUpdate` to find the types
of the fields it rebinds.  An inductive type is a name in the same way: `indNew` resolves it in
`td.is` to find the data types its constructor takes, and `indMatch` to find the constructors it has
to have an alternative for and the types those alternatives bind. -/
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

/-- Infer the types of `es`, in order, or `none` if any one of them is ill typed.

This is mutual with `Expression.infer` because `app` holds a `List Expression`, which is how
`Expression.rec` offers the nesting: one motive for `Expression`, one for `List Expression`. -/
public def Expression.inferList (td : TypeDecls) (ctx : Context) :
    List Expression → Option (List Ty)
  | [] => some []
  | e :: es => do
    let t ← e.infer td ctx
    let ts ← Expression.inferList td ctx es
    some (t :: ts)

/-- Infer the type of each field's expression, keeping the field it belongs to, or `none` if any one
of them is ill typed.

The result is an association list of exactly the fields given, in exactly the order given, which is
what lets `structNew` compare it against a declaration's field list in one step.  `structUpdate`,
which names only some of the fields, reads it with `lookup` instead. -/
public def Expression.inferFields (td : TypeDecls) (ctx : Context) :
    List (FieldName × Expression) → Option (List (FieldName × Ty))
  | [] => some []
  | (f, e) :: fes => do
    let t ← e.infer td ctx
    let fts ← Expression.inferFields td ctx fes
    some ((f, t) :: fts)

/-- Infer the type of each alternative's expression, in the order the alternatives were written, or
`none` if one of them is for a constructor `cs` does not declare, binds the wrong number of names, or
has an ill-typed expression.

The alternatives are walked and the constructor each one names is looked up in `cs`, so where the
declaration put that constructor has nothing to do with where the match put its alternative: an
alternative is checked against *its own* constructor, and the alternatives may therefore be written
in any order.  What the two lists still have to agree on — that there is one alternative per
constructor — is `Expression.altsExhaustive`'s business, since no single step of this walk can see
it.

A constructor's data types are the types of the names its alternative binds — positionally, since
that is what a constructor carries — so the expression is inferred under `xs.zip ts` in front of the
enclosing context, and the bindings shadow it the way a `lam`'s parameters do.

What comes back is one type per alternative rather than one type for the match: they all have to
agree, and comparing them is `Expression.infer`'s business, where the non-empty case is also ruled
on. -/
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

/-- A `listReverse` is typeable exactly when its operand is a list, and then it has that same list
type.

Reversing preserves both the length and the element type, so the operand's type is also the
result's: unlike `lcons`, this form introduces no new type structure. -/
@[simp, grind =] public theorem Expression.infer_listReverse_eq_some {td : TypeDecls}
    {ctx : Context} {l : Expression} {t : Ty} :
    (Expression.listReverse l).infer td ctx = some t ↔
      ∃ t', l.infer td ctx = some (.list t') ∧ t = .list t' := by
  simp only [Expression.infer]
  split <;> grind

/-- A `lam` is typeable exactly when its body is, under its parameters extended with the enclosing
context, and then it is a function from the parameters' types to the body's.

Parameters go on the front of the context, so they shadow same-named bindings from outside, and — as
in `FuncDecl.callEnv` — a name repeated in the parameter list refers to its leftmost occurrence. -/
@[simp, grind =] public theorem Expression.infer_lam_eq_some {td : TypeDecls} {ctx : Context}
    {ps : List (String × Ty)} {body : Expression} {t : Ty} :
    (Expression.lam ps body).infer td ctx = some t ↔
      ∃ r, body.infer td (ps ++ ctx) = some r ∧ t = .fn (ps.map Prod.snd) r := by
  simp [Expression.infer, Option.bind_eq_some_iff]
  grind

/-- An `app` is typeable exactly when its function's type is a function type whose parameter types
are the types of the arguments, in order, and then it is that function type's result.

Because `Ty.fn` records all the parameters at once, arity is part of that one comparison: a call
passing too few arguments is ill typed rather than partially applied. -/
@[simp, grind =] public theorem Expression.infer_app_eq_some {td : TypeDecls} {ctx : Context}
    {f : Expression} {args : List Expression} {t : Ty} :
    (Expression.app f args).infer td ctx = some t ↔
      ∃ ps, f.infer td ctx = some (.fn ps t) ∧ Expression.inferList td ctx args = some ps := by
  simp only [Expression.infer]
  split <;> grind

/-- An `ite` is typeable exactly when its condition is a `bool` and its two branches have one type —
and then that is its type.

The type is read off the branches rather than off the condition, which is what makes the form
polymorphic: a conditional produces whatever its branches produce, so `list`s, functions and structs
are chosen between exactly as `int`s are.  Requiring the two to agree is what leaves the result one
type however the condition comes out, the same thing `Ty.common` asks of an `indMatch`'s alternatives
— stated as one comparison here because there are exactly two of them and the first is the one the
type is taken from. -/
@[simp, grind =] public theorem Expression.infer_ite_eq_some {td : TypeDecls} {ctx : Context}
    {c thn els : Expression} {t : Ty} :
    (Expression.ite c thn els).infer td ctx = some t ↔
      c.infer td ctx = some .bool ∧ thn.infer td ctx = some t ∧ els.infer td ctx = some t := by
  simp [Expression.infer, Option.bind_eq_some_iff, guard]

/-- A `let_` is typeable exactly when the expression it binds is and its body is under that name at
that type, and then it has the body's type.

The bound expression's type is inferred rather than annotated, which is why `let_` carries no `Ty`:
there is nothing for the writer to declare that inference does not already determine.  The name goes
on the front of the context, so it shadows an outer binding of the same name, and the bound
expression is typed *before* it is added, so `let x = x` still refers to the outer `x`. -/
@[simp, grind =] public theorem Expression.infer_let_eq_some {td : TypeDecls} {ctx : Context}
    {x : String} {e body : Expression} {t : Ty} :
    (Expression.let_ x e body).infer td ctx = some t ↔
      ∃ t', e.infer td ctx = some t' ∧ body.infer td ((x, t') :: ctx) = some t := by
  simp [Expression.infer, Option.bind_eq_some_iff]

/-- A `structNew` is typeable exactly when the name it gives is declared and the fields it gives are
that declaration's fields, in that order, at those types — and then it has the struct's type.

One comparison covers everything "all fields must be initialized" asks for: `inferFields` keeps each
field's name beside the type inferred for its expression, so a missing field, a field the declaration
does not have, a repeated field, and a field at the wrong type all make the two lists differ.  It
also fixes the order, so the values `Eval` builds are in the order the declaration wrote its fields.

The type is just the name.  Nothing about the fields survives into it, which is what makes `td.ss`
necessary everywhere a struct is taken apart again. -/
@[simp, grind =] public theorem Expression.infer_structNew_eq_some {td : TypeDecls} {ctx : Context}
    {name : String} {fes : List (FieldName × Expression)} {t : Ty} :
    (Expression.structNew name fes).infer td ctx = some t ↔
      ∃ sd, td.ss.lookup name = some sd ∧ Expression.inferFields td ctx fes = some sd.fields
        ∧ t = .struct name := by
  simp only [Expression.infer]
  split <;> grind

/-- A `structGet` is typeable exactly when its operand is a declared struct with the named field, and
then it has that field's declared type.

Both lookups have to succeed: a struct type whose name is not declared has no fields to read, and a
field the declaration does not list is not a field of it.  There is no structural fallback — a value
that happens to carry the field is still ill typed unless its declaration says so. -/
@[simp, grind =] public theorem Expression.infer_structGet_eq_some {td : TypeDecls} {ctx : Context}
    {e : Expression} {f : FieldName} {t : Ty} :
    (Expression.structGet e f).infer td ctx = some t ↔
      ∃ name sd, e.infer td ctx = some (.struct name) ∧ td.ss.lookup name = some sd
        ∧ sd.fields.lookup f = some t := by
  simp only [Expression.infer]
  split <;> grind

/-- A `structUpdate` is typeable exactly when its operand is a declared struct and every field it
rebinds is one of that declaration's, at the type the declaration gives it — and then it has the same
struct type it started with.

Where `structNew` compares the whole list, this one looks each field up, because an update names only
the fields it changes and may name them in any order.  The list has to be non-empty, as
`Expression.structUpdate` says: an update of nothing is the expression it updates, written in a way
that suggests otherwise.

Updating cannot change a struct's type, so the result type is read off the operand rather than built.
That is what lets updates chain. -/
@[simp, grind =] public theorem Expression.infer_structUpdate_eq_some {td : TypeDecls}
    {ctx : Context} {e : Expression} {fes : List (FieldName × Expression)} {t : Ty} :
    (Expression.structUpdate e fes).infer td ctx = some t ↔
      ∃ name sd fts, e.infer td ctx = some (.struct name) ∧ td.ss.lookup name = some sd
        ∧ Expression.inferFields td ctx fes = some fts ∧ fts ≠ []
        ∧ (∀ p ∈ fts, sd.fields.lookup p.1 = some p.2) ∧ t = .struct name := by
  simp only [Expression.infer]
  split <;> grind

/-- An `indNew` is typeable exactly when the type it names is declared, that declaration has the
constructor it names, and the arguments are the data types that constructor takes, in order — and
then it has the inductive type's type.

Arity is part of that one comparison, the way it is for `app`: a constructor given too few arguments
is ill typed rather than partially applied, and a constructor of no arguments takes exactly none.

The type is just the name.  Which constructor built the value does not survive into it — that is the
whole point of an inductive type — which is what makes `indMatch` the only way to find out again. -/
@[simp, grind =] public theorem Expression.infer_indNew_eq_some {td : TypeDecls} {ctx : Context}
    {name : String} {c : CtorName} {args : List Expression} {t : Ty} :
    (Expression.indNew name c args).infer td ctx = some t ↔
      ∃ d ts, td.is.lookup name = some d ∧ d.constructors.lookup c = some ts
        ∧ Expression.inferList td ctx args = some ts ∧ t = .ind name := by
  simp [Expression.infer, Option.bind_eq_some_iff, guard]
  grind

/-- An `indMatch` is typeable exactly when its scrutinee is a declared inductive type, it has one
alternative per constructor of that declaration, those alternatives all check, and they all have one
type — and then that is its type.

Exhaustiveness and checking are two conditions rather than one because the alternatives may be
written in any order: `Expression.altsExhaustive` says the alternatives are for the declaration's
constructors, one apiece, and `Expression.inferAlts` checks each one against whichever constructor it
names.  What is left here is that the alternatives agree on a type, which they must because the match
has one type however the value was built.

The list of types being non-empty is what rules out a match on a type with no constructors: there
would be no alternative to read a type off, and nothing an expected type could be inferred from.  An
inductive type declaring no constructors is therefore a type nothing can take apart — though nothing
can build a value of it either. -/
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
says what one step along it asks for.  Neither mentions exhaustiveness: running out of alternatives
with constructors left over is not something the walk is in a position to notice, which is why
`Expression.altsExhaustive` is a separate condition. -/

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
data types, and the type inferred for its expression is one of the types `inferAlts` reports.

This is what carries the result of the walk over to a *particular* constructor: `Eval` finds an
alternative by the name the value it took apart carries, and `Value.HasType` finds that name's data
types by looking them up in the declaration.  Both lookups take the leftmost entry of a repeated
name, and the walk resolves each alternative's constructor with the same `lookup` this hypothesis
does, so the types the alternative was checked against are the ones the value is held to — which is
what makes this provable without `InductiveDecl.CtorNamesUnique`, for a declaration repeating a
constructor name as well as for one that does not.

Exhaustiveness is not needed for it.  `Eval` supplies the alternative rather than looking for one, so
what this has to say is what the checker did with an alternative that is *there*; that there is one
for every constructor is `Expression.lookup_isSome_of_altsExhaustive`'s business. -/
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

/-- Check `e` against the expected type `ty` under `ctx`. -/
public def Expression.check (td : TypeDecls) (ctx : Context) (e : Expression) (ty : Ty) : Bool :=
  e.infer td ctx == some ty

/-- `e` is well typed under `ctx` at some type. -/
public def Expression.WellTyped (td : TypeDecls) (ctx : Context) (e : Expression) : Prop :=
  ∃ t, e.check td ctx t = true

/-- Inference is complete for well-typed expressions: since every form carries enough
information to determine its own type, a type exists exactly when `infer` finds one. -/
public theorem Expression.wellTyped_iff_infer_isSome (td : TypeDecls) (ctx : Context)
    (e : Expression) : e.WellTyped td ctx ↔ (e.infer td ctx).isSome := by
  simp [Expression.WellTyped, Expression.check, Option.isSome_iff_exists]

/-! ## Globals

The declarations a body may mention besides its own parameters.  A `Globals` is a table of
*declarations*, not of values: every global is a function, and a global variable is a function of
no arguments, written `g()`.

One mechanism covers both because recursion needs it to.  A table of values would have to be built
before anything could mention it, so a declaration could never refer to itself or to one defined
after it; a table of declarations is just syntax, and a body can be checked against a context
listing every entry including its own. -/

/-- The declarations in scope everywhere, each under the name it is referred to by. -/
public abbrev Globals := List (String × FuncDecl)

/-- Key each declaration by the name it declares. -/
@[expose] public def Globals.ofDecls (ds : List FuncDecl) : Globals := ds.map fun d => (d.name, d)

/-- The type a declaration has where its name is mentioned: a function from its parameters' types
to its result type.

A declaration of no parameters gets `.fn [] t` rather than `t`, which is what makes a global
variable a call. -/
@[expose] public def FuncDecl.ty (d : FuncDecl) : Ty := .fn (d.parameters.map Prod.snd) d.resultType

/-- The context `gs` supplies: every global's name at the type of the declaration stored for it. -/
public def Globals.types : Globals → Context
  | [] => []
  | (x, d) :: gs => (x, d.ty) :: Globals.types gs

@[simp] public theorem Globals.types_nil : Globals.types [] = [] := by simp [Globals.types]

@[simp] public theorem Globals.types_cons (x : String) (d : FuncDecl) (gs : Globals) :
    Globals.types ((x, d) :: gs) = (x, d.ty) :: Globals.types gs := by simp [Globals.types]

/-- `Globals.types` is `FuncDecl.ty` under the lookup, which is how a proof gets from the type a
name was inferred at back to the declaration that gave it. -/
@[simp, grind =] public theorem Globals.lookup_types {gs : Globals} {x : String} :
    (Globals.types gs).lookup x = (gs.lookup x).map FuncDecl.ty := by
  induction gs with
  | nil => rfl
  | cons p gs ih =>
      obtain ⟨k, d⟩ := p
      by_cases h : x == k <;> simp [Globals.types, List.lookup_cons, h, ih]

/-- Check a declaration: its body has to check against the declared result type under its own
parameters over the globals.

The parameters come first, so a parameter shadows a global of the same name.  `Env.lookup` resolves
a name the same way round, and that agreement is what `Eval.hasType` rests on. -/
public def FuncDecl.check (d : FuncDecl) (td : TypeDecls) (gs : Globals) : Bool :=
  d.body.check td (d.parameters ++ Globals.types gs) d.resultType

/-- `d`'s body agrees with the types `d` declares for its parameters and its result, given `td` and
`gs`. -/
public def FuncDecl.WellTyped (d : FuncDecl) (td : TypeDecls) (gs : Globals) : Prop :=
  d.check td gs = true

/-- `FuncDecl.check`'s body is not visible outside this module, so this is how a proof elsewhere
gets at what `WellTyped` says: inference on the body finds exactly the declared result type. -/
@[simp, grind =] public theorem FuncDecl.wellTyped_iff_infer_eq_some {d : FuncDecl} {td : TypeDecls}
    {gs : Globals} :
    d.WellTyped td gs ↔ d.body.infer td (d.parameters ++ Globals.types gs) = some d.resultType := by
  simp [FuncDecl.WellTyped, FuncDecl.check, Expression.check]

/-- Every declaration in `gs` checks, each under a context holding all of them.

Itself included — which is what lets a global call itself, and two globals call each other.  This
is a condition on syntax alone: no value occurs in it.  That is what keeps it provable at all.  A
value-level version would have to type each global's closure, which carries the globals table,
which would need typing again, and no inductive relation survives that regress.

Exposed, unlike the rest of this module's definitions: it is a specification rather than an
algorithm, there is nothing in it for an inversion principle to recover, and every consumer needs to
instantiate it at a name. -/
@[expose] public def Globals.WellTyped (td : TypeDecls) (gs : Globals) : Prop :=
  ∀ x d, gs.lookup x = some d → d.WellTyped td gs

/-- A program with no globals has nothing to check, whatever structs it declares. -/
public theorem Globals.wellTyped_nil {td : TypeDecls} : Globals.WellTyped td [] := by
  intro x d hx; simp at hx

/-- A lookup only ever hands back an entry the table contains. -/
public theorem Globals.mem_of_lookup {gs : Globals} {x : String} {d : FuncDecl}
    (h : gs.lookup x = some d) : (x, d) ∈ gs :=
  List.mem_of_lookup h

/-- A table checks if each of its entries does.

Stated over membership rather than lookup because that is what a table written out as a literal can
be discharged against, one entry at a time. -/
public theorem Globals.wellTyped_of_forall {td : TypeDecls} {gs : Globals}
    (h : ∀ p ∈ gs, FuncDecl.WellTyped p.2 td gs) : Globals.WellTyped td gs :=
  fun x d hx => h (x, d) (Globals.mem_of_lookup hx)

/-- Run the checker over a whole table.  Decides `Globals.WellTyped`, which `#guard` can report on
even where the kernel cannot reduce `Expression.infer`. -/
public def Globals.check (td : TypeDecls) (gs : Globals) : Bool := gs.all fun p => p.2.check td gs

/-- `Globals.check` is what it says it is.  It is the stronger of the two: it checks every entry,
where `Globals.WellTyped` only constrains the ones a lookup can reach. -/
public theorem Globals.wellTyped_of_check {td : TypeDecls} {gs : Globals}
    (h : Globals.check td gs = true) : Globals.WellTyped td gs :=
  Globals.wellTyped_of_forall fun p hp => List.all_eq_true.mp h p hp

@[simp] public theorem Globals.ofDecls_nil : Globals.ofDecls [] = [] := by simp [Globals.ofDecls]

@[simp] public theorem Globals.ofDecls_cons (d : FuncDecl) (ds : List FuncDecl) :
    Globals.ofDecls (d :: ds) = (d.name, d) :: Globals.ofDecls ds := by simp [Globals.ofDecls]

/-- With no repeated names, `Globals.ofDecls` resolves every declaration to itself. -/
public theorem Globals.lookup_ofDecls_self {ds : List FuncDecl} (hu : (ds.map FuncDecl.name).Nodup)
    {d : FuncDecl} (hd : d ∈ ds) : (Globals.ofDecls ds).lookup d.name = some d := by
  simpa [Globals.ofDecls] using List.lookup_keyed_self hu hd

/-- With no repeated names, `Structs.ofDecls` resolves every structure declaration to itself.  This
is what `Program.StructNamesUnique` buys, exactly as `Globals.lookup_ofDecls_self` is what
`Program.NamesUnique` buys. -/
public theorem Structs.lookup_ofDecls_self {sds : List StructDecl}
    (hu : (sds.map StructDecl.name).Nodup) {sd : StructDecl} (hd : sd ∈ sds) :
    (Structs.ofDecls sds).lookup sd.name = some sd := by
  simpa [Structs.ofDecls] using List.lookup_keyed_self hu hd

/-- With no repeated names, `Inductives.ofDecls` resolves every inductive declaration to itself: the
same fact again, for the other table `Program.InductiveNamesUnique` is about. -/
public theorem Inductives.lookup_ofDecls_self {ids : List InductiveDecl}
    (hu : (ids.map InductiveDecl.name).Nodup) {d : InductiveDecl} (hd : d ∈ ids) :
    (Inductives.ofDecls ids).lookup d.name = some d := by
  simpa [Inductives.ofDecls] using List.lookup_keyed_self hu hd

/-! ## Programs

A `Program` is the source-level artifact — a file's worth of declarations — where a `Globals` is the
table those declarations are checked and run against.  `Program.globals` is the bridge.

The definitions below are exposed, unlike the rest of this module's: each is a projection or an
alias with nothing an inversion principle could recover.  `Program.check` is not, for the same
reason `Globals.check` is not — it runs `Expression.infer`, which stays hidden. -/

/-- The globals table `p` presents to its own bodies: each declaration under the name it declares.

Derived rather than stored, so a declaration can never be filed under a name other than its own. -/
@[expose] public def Program.globals (p : Program) : Globals := Globals.ofDecls p.funcDecls

/-- The struct table `p` presents to its own bodies: each structure type under the name it declares.

Derived the same way and for the same reason as `Program.globals`. -/
@[expose] public def Program.structs (p : Program) : Structs := Structs.ofDecls p.structDecls

/-- The inductive table `p` presents to its own bodies: each inductive type under the name it
declares.  Derived the same way and for the same reason as `Program.globals`. -/
@[expose] public def Program.inductives (p : Program) : Inductives :=
  Inductives.ofDecls p.inductiveDecls

/-- The type declarations `p` presents to its own bodies, as the one bundle everything that resolves
a type name takes.

This is what `p` is checked and evaluated against, so a kind of declaration added to `Program` is
added here too and nowhere else. -/
@[expose] public def Program.typeDecls (p : Program) : TypeDecls where
  ss := p.structs
  is := p.inductives

/-- The declaration `x` names in `p`, or `none` if it names nothing. -/
@[expose] public def Program.lookup (p : Program) (x : String) : Option FuncDecl :=
  p.globals.lookup x

/-- The structure type `name` names in `p`, or `none` if it names nothing. -/
@[expose] public def Program.lookupStruct (p : Program) (name : String) : Option StructDecl :=
  p.structs.lookup name

/-- The inductive type `name` names in `p`, or `none` if it names nothing. -/
@[expose] public def Program.lookupInductive (p : Program) (name : String) : Option InductiveDecl :=
  p.inductives.lookup name

/-! ### Uniqueness

Five tables a program is made of and one condition apiece: no two entries of any of them share the
name it is keyed by.  `List.lookup` takes the leftmost entry of a repeated name, so each of these
rules out an entry the order of writing has made dead.

Three of them are across declarations — `NamesUnique`, `StructNamesUnique`, `InductiveNamesUnique`
— and two are inside one: `StructDecl.FieldNamesUnique` and `InductiveDecl.CtorNamesUnique`.  Only
the latter two are part of `Program.check`, and the split is what the surface syntax can do about
each.  A repeated field or constructor is written in the one command that declares the type, so
`lgtm struct` and `lgtm inductive` reject it outright and `Program.check` is the same rejection for
a `Program` built by hand.  A repeated *declaration* name is two commands that cannot see each
other, and what it costs is a program meaning less than it looks like it does rather than a
declaration that is malformed, so those three stay conditions a proof states where it needs the
lookup to resolve. -/

/-- No two declarations share a name.

`Program.lookup` takes the leftmost of a repeated name, so without this a second declaration of a
name already used is dead: `Program.check` still checks it, but nothing can call it.  Soundness does
not need this — a lookup is deterministic either way — but `Program.lookup_self` does, and so does
reading a program as "these declarations" rather than "these declarations, some of them shadowed". -/
@[expose] public def Program.NamesUnique (p : Program) : Prop :=
  (p.funcDecls.map FuncDecl.name).Nodup

public instance (p : Program) : Decidable p.NamesUnique :=
  inferInstanceAs (Decidable (p.funcDecls.map FuncDecl.name).Nodup)

/-- With no repeated names, every declaration in the program is the one its own name resolves to.

This is what turns "`d` is one of `p`'s declarations" into "`d` is callable", which is what carrying
soundness from `Program.WellTyped` to a particular declaration needs. -/
public theorem Program.lookup_self {p : Program} (hu : p.NamesUnique) {d : FuncDecl}
    (hd : d ∈ p.funcDecls) : p.lookup d.name = some d :=
  Globals.lookup_ofDecls_self hu hd

/-- No two structure declarations share a name.

The counterpart of `Program.NamesUnique`, and it matters for the same reason: `Structs.lookup` takes
the leftmost of a repeated name, so a second declaration of a name already used declares a type
nothing can mention.  It matters *more* than `NamesUnique` does, though, because a struct name is
what a `Ty.struct` is: two declarations under one name would make one type with two sets of fields,
and which set a program meant would come down to the order they were written in. -/
@[expose] public def Program.StructNamesUnique (p : Program) : Prop :=
  (p.structDecls.map StructDecl.name).Nodup

public instance (p : Program) : Decidable p.StructNamesUnique :=
  inferInstanceAs (Decidable (p.structDecls.map StructDecl.name).Nodup)

/-- With no repeated names, every structure declaration in the program is the one its own name
resolves to. -/
public theorem Program.lookupStruct_self {p : Program} (hu : p.StructNamesUnique)
    {sd : StructDecl} (hd : sd ∈ p.structDecls) : p.lookupStruct sd.name = some sd :=
  Structs.lookup_ofDecls_self hu hd

/-- No two inductive declarations share a name.

`Program.StructNamesUnique` for the other kind of type declaration, and it matters for the same
reason: a `Ty.ind` is a name, so two declarations under one name would make one type with two sets of
constructors and leave the order they were written in to decide which one a match has to be
exhaustive over. -/
@[expose] public def Program.InductiveNamesUnique (p : Program) : Prop :=
  (p.inductiveDecls.map InductiveDecl.name).Nodup

public instance (p : Program) : Decidable p.InductiveNamesUnique :=
  inferInstanceAs (Decidable (p.inductiveDecls.map InductiveDecl.name).Nodup)

/-- With no repeated names, every inductive declaration in the program is the one its own name
resolves to. -/
public theorem Program.lookupInductive_self {p : Program} (hu : p.InductiveNamesUnique)
    {d : InductiveDecl} (hd : d ∈ p.inductiveDecls) : p.lookupInductive d.name = some d :=
  Inductives.lookup_ofDecls_self hu hd

/-- `sd` declares no field name twice.

The conditions above are about one table of declarations each; this one is inside a single
declaration, because `StructDecl.fields` is a table too — an association list `structGet` and
`structUpdate` read with `List.lookup`, which takes the leftmost entry of a repeated name.  A field
repeating a name already used is therefore one nothing can read and nothing can rebind, while
`structNew` compares its keys positionally and so still makes every value of the type carry it.

It is a condition on the declaration rather than on the program because that is the whole of what
it says: unlike a type name, a field name is scoped to the structure that declares it, so two
structs may each have an `x`. -/
@[expose] public def StructDecl.FieldNamesUnique (sd : StructDecl) : Prop :=
  (sd.fields.map Prod.fst).Nodup

public instance (sd : StructDecl) : Decidable sd.FieldNamesUnique :=
  inferInstanceAs (Decidable (sd.fields.map Prod.fst).Nodup)

/-- With no repeated field names, every field of the declaration is the one its own name resolves
to, at the type written for it.

This is to a declaration's fields what `Program.lookupStruct_self` is to a program's structure
declarations: it turns "`f` is one of `sd`'s fields, at type `t`" into the `lookup` every rule about
a field is stated with. -/
public theorem StructDecl.lookup_field_self {sd : StructDecl} (hu : sd.FieldNamesUnique)
    {f : FieldName} {t : Ty} (hf : (f, t) ∈ sd.fields) : sd.fields.lookup f = some t :=
  List.lookup_of_mem hu hf

/-- `d` declares no constructor name twice.

`StructDecl.FieldNamesUnique` for the other kind of type declaration, and it is inside the
declaration for the same reason: `InductiveDecl.constructors` is an association list `indNew` and
`inferAlts` both read with `List.lookup`, which takes the leftmost entry of a repeated name.  A
constructor repeating a name already used is therefore one nothing can build a value with and no
alternative can be checked against, while `Expression.altsExhaustive` still counts it and so makes
every match on the type write an alternative that can never run.

A constructor name is scoped to its own type in the way a field name is — `indNew` names the type
as well — so two types may each have a `Red`, and one declaration never constrains another. -/
@[expose] public def InductiveDecl.CtorNamesUnique (d : InductiveDecl) : Prop :=
  (d.constructors.map Prod.fst).Nodup

public instance (d : InductiveDecl) : Decidable d.CtorNamesUnique :=
  inferInstanceAs (Decidable (d.constructors.map Prod.fst).Nodup)

/-- With no repeated constructor names, every constructor of the declaration is the one its own name
resolves to, at the data types written for it.

This is to a declaration's constructors what `Program.lookupInductive_self` is to a program's
inductive declarations: it turns "`c` is one of `d`'s constructors, carrying `ts`" into the `lookup`
every rule about a constructor is stated with. -/
public theorem InductiveDecl.lookup_ctor_self {d : InductiveDecl} (hu : d.CtorNamesUnique)
    {c : CtorName} {ts : List Ty} (hc : (c, ts) ∈ d.constructors) :
    d.constructors.lookup c = some ts :=
  List.lookup_of_mem hu hc

/-- No structure declaration in `p` declares the same field name twice.

`StructDecl.FieldNamesUnique` for every declaration at once, which is the form a condition on a
`Program` is in.  Instantiating it at a declaration — `hu sd hd` — is what hands back that
declaration's own condition, and `StructDecl.lookup_field_self` is what that buys. -/
@[expose] public def Program.FieldNamesUnique (p : Program) : Prop :=
  ∀ sd ∈ p.structDecls, sd.FieldNamesUnique

public instance (p : Program) : Decidable p.FieldNamesUnique :=
  inferInstanceAs (Decidable (∀ sd ∈ p.structDecls, sd.FieldNamesUnique))

/-- No inductive declaration in `p` declares the same constructor name twice.

`InductiveDecl.CtorNamesUnique` for every declaration at once, the way `Program.FieldNamesUnique`
is its condition for every structure declaration. -/
@[expose] public def Program.CtorNamesUnique (p : Program) : Prop :=
  ∀ d ∈ p.inductiveDecls, d.CtorNamesUnique

public instance (p : Program) : Decidable p.CtorNamesUnique :=
  inferInstanceAs (Decidable (∀ d ∈ p.inductiveDecls, d.CtorNamesUnique))

/-! ### Checking -/

/-- Check a whole program: the types it declares are well formed, and every declaration checks
against the signatures of all of them, its own included, and against those types.

Well formed is `Program.FieldNamesUnique` and `Program.CtorNamesUnique`: a field or a constructor
declared twice is one the rest of the language cannot reach, so a declaration carrying one is
rejected here rather than left to mean less than it says.  Neither is a condition on any expression,
which is why they are checked once over the declarations instead of anywhere in `Expression.infer`.

The conditions across declarations are not part of this; see the uniqueness section above. -/
public def Program.check (p : Program) : Bool :=
  decide p.FieldNamesUnique && decide p.CtorNamesUnique && Globals.check p.typeDecls p.globals

/-- Every declaration in `p` checks, under `p`. -/
@[expose] public def Program.WellTyped (p : Program) : Prop :=
  Globals.WellTyped p.typeDecls p.globals

/-- `Program.check` is the stronger of the two, as `Globals.check` is: it also has the type
declarations to be well formed, which `Program.WellTyped` says nothing about. -/
public theorem Program.wellTyped_of_check {p : Program} (h : p.check = true) : p.WellTyped := by
  simp only [Program.check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact Globals.wellTyped_of_check h.2

/-- The other half of what `Program.check` decided: no structure declaration repeats a field name.
`Program.check`'s body is not visible outside this module, so this is how a proof gets at it. -/
public theorem Program.fieldNamesUnique_of_check {p : Program} (h : p.check = true) :
    p.FieldNamesUnique := by
  simp only [Program.check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

/-- And no inductive declaration repeats a constructor name. -/
public theorem Program.ctorNamesUnique_of_check {p : Program} (h : p.check = true) :
    p.CtorNamesUnique := by
  simp only [Program.check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

/-- Everything a well-typed program declares is well typed under it. -/
public theorem Program.wellTyped_decl {p : Program} (hp : p.WellTyped) (hu : p.NamesUnique)
    {d : FuncDecl} (hd : d ∈ p.funcDecls) : d.WellTyped p.typeDecls p.globals :=
  hp d.name d (Program.lookup_self hu hd)

section Tests

/-- `struct Point { x : int, y : int }` -/
private def point : StructDecl where
  name := "Point"
  fields := [("x", .int), ("y", .int)]

/-- A struct whose fields cover the other type formers, one of them another struct. -/
private def box : StructDecl where
  name := "Box"
  fields := [("label", .string), ("items", .list .int), ("origin", .struct "Point")]

/-- `inductive Color { Red, Green, Blue }`: an enumeration, which is what an inductive type whose
constructors all carry nothing comes to. -/
private def color : InductiveDecl where
  name := "Color"
  constructors := [("Red", []), ("Green", []), ("Blue", [])]

/-- Constructors carrying data, of one type and of several, one of them a declared struct. -/
private def shape : InductiveDecl where
  name := "Shape"
  constructors := [("Circle", [.int]), ("Rect", [.int, .int]), ("At", [.struct "Point"])]

/-- A recursive type: `Node` carries two more `Tree`s. -/
private def tree : InductiveDecl where
  name := "Tree"
  constructors := [("Leaf", [.int]), ("Node", [.ind "Tree", .ind "Tree"])]

private def types : TypeDecls :=
  { ss := Structs.ofDecls [point, box], is := Inductives.ofDecls [color, shape, tree] }

private def ctx : Context :=
  [("xs", .list .int), ("n", .int), ("s", .string), ("f", .fn [.int, .string] .int),
    ("p", .struct "Point"), ("b", .struct "Box"), ("c", .ind "Color"), ("sh", .ind "Shape"),
    ("t", .ind "Tree"), ("flag", .bool)]

-- Inference determines the type of every form.
#guard (Expression.intLit 3).infer types ctx == some .int
#guard (Expression.stringLit "hi").infer types ctx == some .string
#guard (Expression.varRef "n").infer types ctx == some .int
#guard (Expression.varRef "s").infer types ctx == some .string
#guard (Expression.varRef "xs").infer types ctx == some (.list .int)
#guard (Expression.varRef "f").infer types ctx == some (.fn [.int, .string] .int)
#guard (Expression.varRef "nope").infer types ctx == none
#guard (Expression.plus (.varRef "n") (.intLit 1)).infer types ctx == some .int
#guard (Expression.minus (.intLit 1) (.varRef "xs")).infer types ctx == none

-- Arithmetic is on `int`s only: a string operand is rejected on either side.
#guard (Expression.plus (.stringLit "a") (.stringLit "b")).infer types ctx == none
#guard (Expression.plus (.varRef "n") (.stringLit "b")).infer types ctx == none
#guard (Expression.minus (.stringLit "a") (.varRef "n")).infer types ctx == none

-- An empty list takes its type from its annotation, not from its context.
#guard (Expression.lnil .int).infer types ctx == some (.list .int)
#guard (Expression.lnil (.list .int)).infer types ctx == some (.list (.list .int))

-- A non-empty list takes its element type from its head, and its tail has to agree.
#guard (Expression.lcons (.intLit 1) (.lnil .int)).infer types ctx == some (.list .int)
#guard (Expression.lcons (.intLit 1) (.varRef "xs")).infer types ctx == some (.list .int)
#guard (Expression.lcons (.varRef "xs") (.lnil (.list .int))).infer types ctx
  == some (.list (.list .int))
#guard (Expression.lcons (.intLit 1) (.intLit 2)).infer types ctx == none
#guard (Expression.lcons (.intLit 1) (.lnil (.list .int))).infer types ctx == none
#guard (Expression.lcons (.varRef "xs") (.varRef "xs")).infer types ctx == none

-- Lists are homogeneous across the new type too, so a mixed list has no type.
#guard (Expression.lcons (.stringLit "a") (.lnil .string)).infer types ctx == some (.list .string)
#guard (Expression.lcons (.stringLit "a") (.lnil .int)).infer types ctx == none
#guard (Expression.lcons (.intLit 1) (.lnil .string)).infer types ctx == none
#guard (Expression.lcons (.stringLit "a") (.varRef "xs")).infer types ctx == none

-- A list of empty lists needs no expected type to be inferred, only agreeing annotations.
#guard (Expression.lcons (.lnil .int) (.lnil (.list .int))).infer types ctx
  == some (.list (.list .int))
#guard (Expression.lcons (.lnil .int) (.lnil .int)).infer types ctx == none

-- Reversing a list keeps its type, whatever the element type is.
#guard (Expression.listReverse (.varRef "xs")).infer types ctx == some (.list .int)
#guard (Expression.listReverse (.lnil .string)).infer types ctx == some (.list .string)
#guard (Expression.listReverse (.lcons (.intLit 1) (.lnil .int))).infer types ctx
  == some (.list .int)
#guard (Expression.listReverse (.lnil (.list .int))).infer types ctx == some (.list (.list .int))

-- Only a list can be reversed, so a non-list operand is ill typed rather than passed through.
#guard (Expression.listReverse (.intLit 1)).infer types ctx == none
#guard (Expression.listReverse (.stringLit "a")).infer types ctx == none
#guard (Expression.listReverse (.varRef "n")).infer types ctx == none
#guard (Expression.listReverse (.varRef "f")).infer types ctx == none

-- An ill-typed operand makes the whole reversal ill typed.
#guard (Expression.listReverse (.varRef "nope")).infer types ctx == none
#guard (Expression.listReverse (.lcons (.intLit 1) (.lnil .string))).infer types ctx == none

-- Reversals nest, since each one gives back a list.
#guard (Expression.listReverse (.listReverse (.varRef "xs"))).infer types ctx == some (.list .int)
#guard (Expression.listReverse (.listReverse (.intLit 1))).infer types ctx == none

-- A `lam` takes its parameter types from its annotation and its result type from its body.
#guard (Expression.lam [("x", .int)] (.varRef "x")).infer types ctx == some (.fn [.int] .int)
#guard (Expression.lam [("x", .int), ("y", .string)] (.varRef "y")).infer types ctx
  == some (.fn [.int, .string] .string)
#guard (Expression.lam [] (.intLit 1)).infer types ctx == some (.fn [] .int)
#guard (Expression.lam [("x", .int)] (.varRef "nope")).infer types ctx == none
#guard (Expression.lam [("x", .string)] (.plus (.varRef "x") (.intLit 1))).infer types ctx == none

-- A body sees the enclosing context as well as the parameters, and the parameters shadow it.
#guard (Expression.lam [("x", .int)] (.plus (.varRef "x") (.varRef "n"))).infer types ctx
  == some (.fn [.int] .int)
#guard (Expression.lam [("n", .string)] (.varRef "n")).infer types ctx
  == some (.fn [.string] .string)
#guard (Expression.lam [("x", .int), ("x", .string)] (.varRef "x")).infer types ctx
  == some (.fn [.int, .string] .int)

-- Function types are types like any other: a `lam` can return one, and a list can hold them.
#guard (Expression.lam [("x", .int)] (.lam [("y", .string)] (.varRef "x"))).infer types ctx
  == some (.fn [.int] (.fn [.string] .int))
#guard (Expression.lcons (.varRef "f") (.lnil (.fn [.int, .string] .int))).infer types ctx
  == some (.list (.fn [.int, .string] .int))
#guard (Expression.lcons (.varRef "f") (.lnil (.fn [.int] .int))).infer types ctx == none

-- An `app` needs a function, and arguments whose types are the parameter types in order.
#guard (Expression.app (.varRef "f") [.intLit 1, .stringLit "a"]).infer types ctx == some .int
#guard (Expression.app (.lam [("x", .int)] (.plus (.varRef "x") (.intLit 1)))
  [.intLit 2]).infer types ctx == some .int
#guard (Expression.app (.lam [] (.intLit 1)) []).infer types ctx == some .int
#guard (Expression.app (.varRef "f") [.stringLit "a", .intLit 1]).infer types ctx == none
#guard (Expression.app (.varRef "f") [.varRef "nope", .stringLit "a"]).infer types ctx == none
#guard (Expression.app (.varRef "n") [.intLit 1]).infer types ctx == none
#guard (Expression.app (.lnil .int) []).infer types ctx == none

-- Arity is part of the function type, so a call with the wrong number of arguments is ill typed
-- rather than partially applied.
#guard (Expression.app (.varRef "f") [.intLit 1]).infer types ctx == none
#guard (Expression.app (.varRef "f") []).infer types ctx == none
#guard (Expression.app (.varRef "f") [.intLit 1, .stringLit "a", .intLit 2]).infer types ctx
  == none

-- Applying a function that returns a function gives the inner function type, which can then be
-- applied in turn.
#guard (Expression.app (.lam [("x", .int)] (.lam [("y", .string)] (.varRef "x"))) [.intLit 1]).infer
  types ctx == some (.fn [.string] .int)
#guard (Expression.app (.app (.lam [("x", .int)] (.lam [("y", .string)] (.varRef "x"))) [.intLit 1])
  [.stringLit "a"]).infer types ctx == some .int

-- A `let_` gives its body's type, with the bound name at the type inferred for what it binds.
#guard (Expression.let_ "x" (.intLit 1) (.plus (.varRef "x") (.intLit 2))).infer types ctx
  == some .int
#guard (Expression.let_ "x" (.stringLit "a") (.varRef "x")).infer types ctx == some .string
#guard (Expression.let_ "x" (.varRef "xs") (.varRef "x")).infer types ctx == some (.list .int)
#guard (Expression.let_ "g" (.lam [("y", .int)] (.varRef "y"))
  (.app (.varRef "g") [.intLit 1])).infer types ctx == some .int

-- An ill-typed expression on either side makes the whole `let_` ill typed.
#guard (Expression.let_ "x" (.varRef "nope") (.intLit 1)).infer types ctx == none
#guard (Expression.let_ "x" (.intLit 1) (.plus (.varRef "x") (.stringLit "a"))).infer types ctx
  == none
#guard (Expression.let_ "x" (.intLit 1) (.varRef "nope")).infer types ctx == none

-- The name is added after the expression it binds is typed, so a `let_` is not recursive: the bound
-- expression sees the enclosing context only.
#guard (Expression.let_ "x" (.varRef "x") (.varRef "x")).infer types ctx == none
#guard (Expression.let_ "n" (.plus (.varRef "n") (.intLit 1)) (.varRef "n")).infer types ctx
  == some .int

-- The binding shadows an enclosing one of the same name, inner `let_`s included.
#guard (Expression.let_ "n" (.stringLit "a") (.varRef "n")).infer types ctx == some .string
#guard (Expression.let_ "n" (.stringLit "a") (.plus (.varRef "n") (.intLit 1))).infer types ctx
  == none
#guard (Expression.let_ "x" (.intLit 1)
  (.let_ "x" (.stringLit "a") (.varRef "x"))).infer types ctx == some .string

-- `let_`s nest, and a later one sees what an earlier one bound.
#guard (Expression.let_ "x" (.intLit 1)
  (.let_ "y" (.plus (.varRef "x") (.intLit 1))
    (.plus (.varRef "x") (.varRef "y")))).infer types ctx == some .int

-- A `lam` body sees a `let_` from outside it, and a `let_` body sees the parameters.
#guard (Expression.let_ "x" (.intLit 1)
  (.lam [("y", .int)] (.plus (.varRef "x") (.varRef "y")))).infer types ctx
  == some (.fn [.int] .int)
#guard (Expression.lam [("y", .int)]
  (.let_ "x" (.varRef "y") (.plus (.varRef "x") (.varRef "y")))).infer types ctx
  == some (.fn [.int] .int)

/-! ### Booleans and conditionals

A `bool` is a type like any other — it nests under `list`, appears in a function type, and is distinct
from everything else.  Two forms mention it: `boolLit`, which is where one comes from, and `ite`,
which is what one is for. -/

#guard Ty.bool == Ty.bool
#guard Ty.bool != Ty.int
#guard (Expression.varRef "flag").infer types ctx == some .bool
#guard (Expression.lcons (.varRef "flag") (.lnil .bool)).infer types ctx == some (.list .bool)
#guard (Expression.lcons (.varRef "flag") (.lnil .int)).infer types ctx == none

-- A literal determines its own type, as `intLit` and `stringLit` do, and both of them are the same
-- type: which `Bool` it carries is not something `Ty.bool` has heard about.
#guard (Expression.boolLit true).infer types ctx == some .bool
#guard (Expression.boolLit false).infer types ctx == some .bool
#guard (Expression.boolLit true).infer {} [] == some .bool
#guard (Expression.boolLit true).check types ctx .bool
#guard !(Expression.boolLit true).check types ctx .int
#guard !(Expression.boolLit false).check types ctx (.list .bool)

-- So a literal goes wherever a `bool` goes: into a list of them, into a conditional's branches, and
-- into a call expecting one.
#guard (Expression.lcons (.boolLit true) (.lnil .bool)).infer types ctx == some (.list .bool)
#guard (Expression.lcons (.boolLit true) (.lcons (.varRef "flag") (.lnil .bool))).infer types ctx
  == some (.list .bool)
#guard (Expression.lcons (.boolLit true) (.lnil .int)).infer types ctx == none
#guard (Expression.app (.lam [("q", .bool)] (.varRef "q")) [.boolLit true]).infer types ctx
  == some .bool
#guard (Expression.app (.lam [("q", .int)] (.varRef "q")) [.boolLit true]).infer types ctx == none
#guard (Expression.plus (.boolLit true) (.intLit 1)).infer types ctx == none

-- A conditional takes its type from its branches, whatever type that is.
#guard (Expression.ite (.varRef "flag") (.intLit 1) (.intLit 2)).infer types ctx == some .int
#guard (Expression.ite (.varRef "flag") (.stringLit "a") (.varRef "s")).infer types ctx
  == some .string
#guard (Expression.ite (.varRef "flag") (.varRef "xs") (.lnil .int)).infer types ctx
  == some (.list .int)
#guard (Expression.ite (.varRef "flag") (.varRef "p") (.varRef "p")).infer types ctx
  == some (.struct "Point")
#guard (Expression.ite (.varRef "flag") (.varRef "c") (.indNew "Color" "Red" [])).infer types ctx
  == some (.ind "Color")
#guard (Expression.ite (.varRef "flag") (.varRef "f") (.varRef "f")).infer types ctx
  == some (.fn [.int, .string] .int)
#guard (Expression.ite (.varRef "flag") (.varRef "flag") (.varRef "flag")).infer types ctx
  == some .bool

-- The two branches have to agree, since the conditional has one type however the condition comes out.
#guard (Expression.ite (.varRef "flag") (.intLit 1) (.stringLit "a")).infer types ctx == none
#guard (Expression.ite (.varRef "flag") (.varRef "p") (.varRef "b")).infer types ctx == none
#guard (Expression.ite (.varRef "flag") (.lnil .int) (.lnil .string)).infer types ctx == none
#guard (Expression.ite (.varRef "flag") (.varRef "flag") (.intLit 1)).infer types ctx == none

-- A literal is what lets a conditional be written without a `bool` in scope, so this is the first
-- form the checker can decide on its own.  Which literal it is makes no difference: a `bool` is a
-- `bool`, and both branches are checked either way.
#guard (Expression.ite (.boolLit true) (.intLit 1) (.intLit 2)).infer types ctx == some .int
#guard (Expression.ite (.boolLit false) (.intLit 1) (.intLit 2)).infer types ctx == some .int
#guard (Expression.ite (.boolLit true) (.intLit 1) (.stringLit "a")).infer types ctx == none
#guard (Expression.ite (.boolLit true) (.intLit 1) (.varRef "nope")).infer types ctx == none
#guard (Expression.ite (.boolLit true) (.boolLit false) (.varRef "flag")).infer types ctx
  == some .bool
#guard (Expression.ite (.boolLit true) (.intLit 1) (.intLit 2)).infer {} [] == some .int

-- And the condition has to be a `bool`: there is no truthiness, so nothing else will do.
#guard (Expression.ite (.intLit 1) (.intLit 1) (.intLit 2)).infer types ctx == none
#guard (Expression.ite (.varRef "n") (.intLit 1) (.intLit 2)).infer types ctx == none
#guard (Expression.ite (.varRef "s") (.intLit 1) (.intLit 2)).infer types ctx == none
#guard (Expression.ite (.varRef "xs") (.intLit 1) (.intLit 2)).infer types ctx == none
#guard (Expression.ite (.varRef "c") (.intLit 1) (.intLit 2)).infer types ctx == none

-- An ill-typed part anywhere makes the whole conditional ill typed, branch not taken included.
#guard (Expression.ite (.varRef "nope") (.intLit 1) (.intLit 2)).infer types ctx == none
#guard (Expression.ite (.varRef "flag") (.varRef "nope") (.intLit 2)).infer types ctx == none
#guard (Expression.ite (.varRef "flag") (.intLit 1) (.varRef "nope")).infer types ctx == none

-- A conditional is an expression like any other, in the condition and in the branches alike.
#guard (Expression.plus (.ite (.varRef "flag") (.intLit 1) (.intLit 2)) (.intLit 1)).infer types ctx
  == some .int
#guard (Expression.ite (.ite (.varRef "flag") (.varRef "flag") (.varRef "flag"))
  (.intLit 1) (.intLit 2)).infer types ctx == some .int
#guard (Expression.ite (.varRef "flag")
  (.ite (.varRef "flag") (.intLit 1) (.intLit 2)) (.intLit 3)).infer types ctx == some .int
#guard (Expression.lam [("q", .bool)] (.ite (.varRef "q") (.intLit 1) (.intLit 2))).infer types ctx
  == some (.fn [.bool] .int)
#guard (Expression.let_ "q" (.varRef "flag")
  (.ite (.varRef "q") (.intLit 1) (.intLit 2))).infer types ctx == some .int
#guard (Expression.indMatch (.varRef "c")
  [("Red", [], .ite (.varRef "flag") (.intLit 0) (.intLit 1)), ("Green", [], .intLit 1),
    ("Blue", [], .intLit 2)]).infer types ctx == some .int

-- Checking agrees with inference.
#guard (Expression.lnil .int).check types ctx (.list .int)
#guard !(Expression.lnil .int).check types ctx .int
#guard (Expression.plus (.varRef "n") (.intLit 1)).check types ctx .int
#guard !(Expression.plus (.varRef "n") (.intLit 1)).check types ctx (.list .int)
#guard !(Expression.plus (.varRef "n") (.lnil .int)).check types ctx .int
#guard (Expression.stringLit "hi").check types ctx .string
#guard !(Expression.stringLit "hi").check types ctx .int
#guard (Expression.lam [("x", .int)] (.varRef "x")).check types ctx (.fn [.int] .int)
#guard !(Expression.lam [("x", .int)] (.varRef "x")).check types ctx (.fn [.string] .string)
#guard !(Expression.lam [("x", .int)] (.varRef "x")).check types ctx .int

/-- `fun (x : int) (y : int) => x + (y - 1)` -/
private def addPred : FuncDecl where
  docstring := "Add `x` to one less than `y`."
  name := "add-pred"
  parameters := [("x", .int), ("y", .int)]
  body := .plus (.varRef "x") (.minus (.varRef "y") (.intLit 1))
  resultType := .int

-- A declaration checks when its body agrees with the result type it declares.
#guard addPred.check {} []
#guard !({ addPred with resultType := .list .int } : FuncDecl).check {} []

-- The parameter list is all the body has to work with, and it is checked at the types it gives.
#guard !({ addPred with parameters := [("x", .int)] } : FuncDecl).check {} []
#guard !({ addPred with parameters := [("x", .int), ("y", .list .int)] } : FuncDecl).check {} []

/-- `fun (s : string) => ["!", s]` -/
private def bang : FuncDecl where
  docstring := "Put `s` after an exclamation mark."
  name := "bang"
  parameters := [("s", .string)]
  body := .lcons (.stringLit "!") (.lcons (.varRef "s") (.lnil .string))
  resultType := .list .string

#guard bang.check {} []
#guard !({ bang with resultType := .list .int } : FuncDecl).check {} []
#guard !({ bang with parameters := [("s", .int)] } : FuncDecl).check {} []

/-- `fun (g : (int) -> int) (x : int) => g(x)` -/
private def applyTo : FuncDecl where
  docstring := "Call `g` on `x`."
  name := "apply-to"
  parameters := [("g", .fn [.int] .int), ("x", .int)]
  body := .app (.varRef "g") [.varRef "x"]
  resultType := .int

-- A parameter of function type is callable, at the arity and types its type gives.
#guard applyTo.check {} []
#guard !({ applyTo with parameters := [("g", .fn [.string] .int), ("x", .int)] }
  : FuncDecl).check {} []
#guard !({ applyTo with parameters := [("g", .fn [.int, .int] .int), ("x", .int)] }
  : FuncDecl).check {} []
#guard !({ applyTo with resultType := .string } : FuncDecl).check {} []

/-- `fun (n : int) => fun (m : int) => n + m` -/
private def adder : FuncDecl where
  docstring := "Build a function that adds `n` to its argument."
  name := "adder"
  parameters := [("n", .int)]
  body := .lam [("m", .int)] (.plus (.varRef "n") (.varRef "m"))
  resultType := .fn [.int] .int

-- A declaration can return a function, and its result type is checked like any other.
#guard adder.check {} []
#guard !({ adder with resultType := .int } : FuncDecl).check {} []
#guard !({ adder with resultType := .fn [.string] .int } : FuncDecl).check {} []

/-! ### Structs

`point` and `box` are the declarations `types` holds, and `ctx` gives `p` and `b` one of each.
`pair` below is declared nowhere: it is what a struct type that names nothing looks like. -/

/-- The same fields as `point` under another name, which is how nominality gets tested: nothing a
`Pair` can do is something a `Point` can do. -/
private def pair : StructDecl where
  name := "Pair"
  fields := [("x", .int), ("y", .int)]

-- A struct type is nominal, so two declarations with identical fields are unrelated types and a
-- list cannot hold one of each.
#guard Ty.struct "Point" == Ty.struct "Point"
#guard Ty.struct "Point" != Ty.struct "Pair"
#guard (Expression.lcons (.varRef "p") (.lnil (.struct "Point"))).infer types ctx
  == some (.list (.struct "Point"))
#guard (Expression.lcons (.varRef "p") (.lnil (.struct "Pair"))).infer types ctx == none

-- A `structNew` initializing every declared field, in the declared order and at the declared types,
-- has the struct's type.
#guard (Expression.structNew "Point" [("x", .intLit 1), ("y", .intLit 2)]).infer types ctx
  == some (.struct "Point")
#guard (Expression.structNew "Point"
  [("x", .varRef "n"), ("y", .plus (.varRef "n") (.intLit 1))]).infer types ctx
  == some (.struct "Point")
#guard (Expression.structNew "Box"
  [("label", .stringLit "b"), ("items", .varRef "xs"), ("origin", .varRef "p")]).infer types ctx
  == some (.struct "Box")

-- Every field has to be there, once, at the right type, and in the order the declaration wrote them.
#guard (Expression.structNew "Point" [("x", .intLit 1)]).infer types ctx == none
#guard (Expression.structNew "Point" []).infer types ctx == none
#guard (Expression.structNew "Point" [("y", .intLit 2), ("x", .intLit 1)]).infer types ctx == none
#guard (Expression.structNew "Point" [("x", .intLit 1), ("y", .intLit 2), ("z", .intLit 3)]).infer
  types ctx == none
#guard (Expression.structNew "Point" [("x", .intLit 1), ("x", .intLit 2)]).infer types ctx == none
#guard (Expression.structNew "Point" [("x", .intLit 1), ("y", .stringLit "a")]).infer types ctx
  == none
#guard (Expression.structNew "Point" [("x", .intLit 1), ("y", .varRef "nope")]).infer types ctx
  == none

-- A name the table does not declare is not a struct at all, however plausible its fields look.
#guard (Expression.structNew "Pair" [("x", .intLit 1), ("y", .intLit 2)]).infer types ctx == none
#guard (Expression.structNew "Point" [("x", .intLit 1), ("y", .intLit 2)]).infer {} ctx == none

-- `structGet` gives the field its declaration gives, whatever type that is.
#guard (Expression.structGet (.varRef "p") "x").infer types ctx == some .int
#guard (Expression.structGet (.varRef "b") "label").infer types ctx == some .string
#guard (Expression.structGet (.varRef "b") "items").infer types ctx == some (.list .int)
#guard (Expression.structGet (.varRef "b") "origin").infer types ctx == some (.struct "Point")

-- So reads chain, and what comes back is usable as the type it has.
#guard (Expression.structGet (.structGet (.varRef "b") "origin") "y").infer types ctx == some .int
#guard (Expression.plus (.structGet (.varRef "p") "x") (.intLit 1)).infer types ctx == some .int
#guard (Expression.listReverse (.structGet (.varRef "b") "items")).infer types ctx
  == some (.list .int)
#guard (Expression.structGet (.structNew "Point" [("x", .intLit 1), ("y", .intLit 2)]) "x").infer
  types ctx == some .int

-- A field the declaration does not list is not a field, and only a struct has fields at all.
#guard (Expression.structGet (.varRef "p") "z").infer types ctx == none
#guard (Expression.structGet (.varRef "b") "x").infer types ctx == none
#guard (Expression.structGet (.varRef "n") "x").infer types ctx == none
#guard (Expression.structGet (.varRef "xs") "x").infer types ctx == none
#guard (Expression.structGet (.varRef "f") "x").infer types ctx == none
#guard (Expression.structGet (.varRef "nope") "x").infer types ctx == none
#guard (Expression.structGet (.varRef "p") "x").infer {} ctx == none

-- `structUpdate` keeps the type it was given, and may name its fields in any order.
#guard (Expression.structUpdate (.varRef "p") [("x", .intLit 1)]).infer types ctx
  == some (.struct "Point")
#guard (Expression.structUpdate (.varRef "p")
  [("y", .intLit 2), ("x", .intLit 1)]).infer types ctx == some (.struct "Point")
#guard (Expression.structUpdate (.varRef "b") [("origin", .varRef "p")]).infer types ctx
  == some (.struct "Box")

-- Which is what lets updates chain, and lets one be read straight away.
#guard (Expression.structUpdate (.structUpdate (.varRef "p") [("x", .intLit 1)])
  [("y", .intLit 2)]).infer types ctx == some (.struct "Point")
#guard (Expression.structGet (.structUpdate (.varRef "p") [("x", .intLit 1)]) "x").infer types ctx
  == some .int

-- Only a declared field, only at its declared type, and never none of them.
#guard (Expression.structUpdate (.varRef "p") []).infer types ctx == none
#guard (Expression.structUpdate (.varRef "p") [("z", .intLit 1)]).infer types ctx == none
#guard (Expression.structUpdate (.varRef "p") [("x", .stringLit "a")]).infer types ctx == none
#guard (Expression.structUpdate (.varRef "p")
  [("x", .intLit 1), ("z", .intLit 2)]).infer types ctx == none
#guard (Expression.structUpdate (.varRef "p") [("x", .varRef "nope")]).infer types ctx == none
#guard (Expression.structUpdate (.varRef "n") [("x", .intLit 1)]).infer types ctx == none
#guard (Expression.structUpdate (.varRef "p") [("x", .intLit 1)]).infer {} ctx == none

/-- `fun (p : Point) => new Point { x = p.y, y = p.x }` -/
private def swap : FuncDecl where
  docstring := "Swap `p`'s coordinates."
  name := "swap"
  parameters := [("p", .struct "Point")]
  body := .structNew "Point"
    [("x", .structGet (.varRef "p") "y"), ("y", .structGet (.varRef "p") "x")]
  resultType := .struct "Point"

-- A declaration takes and returns types like any other type, and it is the struct table rather
-- than the globals that has to supply the declaration its parameter names.
#guard swap.check types []
#guard !swap.check {} []
#guard !({ swap with resultType := .struct "Pair" } : FuncDecl).check types []

/-- `fun (p : Point) => { p with x = p.x + 1 }` -/
private def shift : FuncDecl where
  docstring := "Move `p` one step along the x axis."
  name := "shift"
  parameters := [("p", .struct "Point")]
  body := .structUpdate (.varRef "p") [("x", .plus (.structGet (.varRef "p") "x") (.intLit 1))]
  resultType := .struct "Point"

#guard shift.check types []
#guard !shift.check {} []

/-! ### Distinct field names

What `StructDecl.FieldNamesUnique` asks of a declaration, and what a declaration failing it looks
like.  `Program.check` is where it is enforced, so `Expression.infer` is still willing to work over
`twoXs` below — which is what the guards under it are about. -/

example : point.FieldNamesUnique := by decide
example : box.FieldNamesUnique := by decide

-- Which is what makes every field reachable: being one of the declaration's fields is enough to be
-- the one its own name resolves to, at the type written for it.
example : box.fields.lookup "items" = some (.list .int) :=
  box.lookup_field_self (by simp [StructDecl.FieldNamesUnique, box]) (by simp [box])

/-- Two fields under one name, which is what the condition rules out. -/
private def twoXs : StructDecl where
  name := "TwoXs"
  fields := [("x", .int), ("x", .string)]

example : ¬ twoXs.FieldNamesUnique := by decide

private def twoXTypes : TypeDecls := { ss := Structs.ofDecls [twoXs] }

-- `structNew` compares its own keys against the declaration's positionally, so a value of `TwoXs`
-- can be built, and it has to initialize the name twice, at both declared types in order.
#guard (Expression.structNew "TwoXs" [("x", .intLit 1)]).infer twoXTypes [] == none
#guard (Expression.structNew "TwoXs" [("x", .intLit 1), ("x", .stringLit "a")]).infer twoXTypes []
  == some (.struct "TwoXs")
#guard (Expression.structNew "TwoXs" [("x", .intLit 1), ("x", .intLit 2)]).infer twoXTypes []
  == none

-- What is dead is the second field itself: `structGet` and `structUpdate` resolve the name with
-- `List.lookup`, which stops at the first, so the `string` half of every `TwoXs` is written when
-- one is built and can never be read back or rebound.
#guard (Expression.structGet (.varRef "t") "x").infer twoXTypes [("t", .struct "TwoXs")]
  == some .int
#guard (Expression.structUpdate (.varRef "t") [("x", .stringLit "a")]).infer twoXTypes
  [("t", .struct "TwoXs")] == none
#guard (Expression.structUpdate (.varRef "t") [("x", .intLit 1)]).infer twoXTypes
  [("t", .struct "TwoXs")] == some (.struct "TwoXs")

/-! ### Inductive types

`color`, `shape` and `tree` are the declarations `types` holds, and `ctx` gives `c`, `sh` and `t` one
of each.  `hue` below is declared nowhere: it is what an inductive type that names nothing looks
like. -/

/-- The same constructors as `color` under another name: nominality again, for the other kind of
type declaration. -/
private def hue : InductiveDecl where
  name := "Hue"
  constructors := [("Red", []), ("Green", []), ("Blue", [])]

#guard Ty.ind "Color" == Ty.ind "Color"
#guard Ty.ind "Color" != Ty.ind "Hue"
#guard Ty.ind "Point" != Ty.struct "Point"
#guard (Expression.lcons (.varRef "c") (.lnil (.ind "Color"))).infer types ctx
  == some (.list (.ind "Color"))
#guard (Expression.lcons (.varRef "c") (.lnil (.ind "Hue"))).infer types ctx == none

-- A constructor application gives the type it belongs to, whatever that constructor carries.
#guard (Expression.indNew "Color" "Red" []).infer types ctx == some (.ind "Color")
#guard (Expression.indNew "Shape" "Circle" [.intLit 1]).infer types ctx == some (.ind "Shape")
#guard (Expression.indNew "Shape" "Rect" [.varRef "n", .plus (.varRef "n") (.intLit 1)]).infer
  types ctx == some (.ind "Shape")
#guard (Expression.indNew "Shape" "At" [.varRef "p"]).infer types ctx == some (.ind "Shape")

-- The arguments have to be the data types it declares, in that order and no other number of them.
#guard (Expression.indNew "Color" "Red" [.intLit 1]).infer types ctx == none
#guard (Expression.indNew "Shape" "Circle" []).infer types ctx == none
#guard (Expression.indNew "Shape" "Rect" [.intLit 1]).infer types ctx == none
#guard (Expression.indNew "Shape" "Rect" [.intLit 1, .intLit 2, .intLit 3]).infer types ctx == none
#guard (Expression.indNew "Shape" "Circle" [.stringLit "a"]).infer types ctx == none
#guard (Expression.indNew "Shape" "At" [.varRef "b"]).infer types ctx == none
#guard (Expression.indNew "Shape" "Circle" [.varRef "nope"]).infer types ctx == none

-- A constructor belongs to the type that declares it, and a name the table does not declare is not
-- a type at all — however plausible its constructors look.
#guard (Expression.indNew "Shape" "Red" []).infer types ctx == none
#guard (Expression.indNew "Color" "Purple" []).infer types ctx == none
#guard (Expression.indNew "Hue" "Red" []).infer types ctx == none
#guard (Expression.indNew "Color" "Red" []).infer {} ctx == none

-- A recursive constructor needs nothing further: `Tree` is in scope in its own declaration, because
-- resolving the name happens here rather than when it was declared.
#guard (Expression.indNew "Tree" "Leaf" [.intLit 1]).infer types ctx == some (.ind "Tree")
#guard (Expression.indNew "Tree" "Node"
  [.varRef "t", .indNew "Tree" "Leaf" [.intLit 1]]).infer types ctx == some (.ind "Tree")
#guard (Expression.indNew "Tree" "Node" [.varRef "t", .intLit 1]).infer types ctx == none

-- A `match` gives the type its alternatives agree on, with each alternative's names bound to what
-- its constructor carries.
#guard (Expression.indMatch (.varRef "c")
  [("Red", [], .intLit 0), ("Green", [], .intLit 1), ("Blue", [], .intLit 2)]).infer types ctx
  == some .int
#guard (Expression.indMatch (.varRef "sh")
  [("Circle", ["r"], .varRef "r"), ("Rect", ["w", "h"], .plus (.varRef "w") (.varRef "h")),
    ("At", ["q"], .structGet (.varRef "q") "x")]).infer types ctx == some .int
#guard (Expression.indMatch (.varRef "c")
  [("Red", [], .stringLit "r"), ("Green", [], .stringLit "g"),
    ("Blue", [], .stringLit "b")]).infer types ctx == some .string

-- The alternatives may be in any order at all: each one is checked against the constructor it names
-- rather than against the one at its position, so every arrangement of them has the same type.
#guard (Expression.indMatch (.varRef "c")
  [("Red", [], .intLit 0), ("Blue", [], .intLit 2), ("Green", [], .intLit 1)]).infer types ctx
  == some .int
#guard (Expression.indMatch (.varRef "c")
  [("Blue", [], .intLit 2), ("Green", [], .intLit 1), ("Red", [], .intLit 0)]).infer types ctx
  == some .int
#guard (Expression.indMatch (.varRef "c")
  [("Green", [], .stringLit "g"), ("Blue", [], .stringLit "b"),
    ("Red", [], .stringLit "r")]).infer types ctx == some .string

-- An alternative out of order binds the names its own constructor declares, at that constructor's
-- data types, rather than those of whichever constructor its position would have paired it with.
#guard (Expression.indMatch (.varRef "sh")
  [("Rect", ["w", "h"], .plus (.varRef "w") (.varRef "h")),
    ("At", ["q"], .structGet (.varRef "q") "x"),
    ("Circle", ["r"], .varRef "r")]).infer types ctx == some .int
#guard (Expression.indMatch (.varRef "sh")
  [("Rect", ["w", "h"], .varRef "w"), ("At", ["q"], .intLit 0),
    ("Circle", ["r", "r'"], .varRef "r")]).infer types ctx == none
#guard (Expression.indMatch (.varRef "sh")
  [("At", ["q"], .structGet (.varRef "q") "z"), ("Circle", ["r"], .intLit 0),
    ("Rect", ["w", "h"], .intLit 0)]).infer types ctx == none

-- Exhaustive all the same, and no alternative twice or for a constructor the declaration does not
-- have: reordering is all that is permitted.
#guard (Expression.indMatch (.varRef "c") [("Red", [], .intLit 0)]).infer types ctx == none
#guard (Expression.indMatch (.varRef "c")
  [("Blue", [], .intLit 2), ("Green", [], .intLit 1)]).infer types ctx == none
#guard (Expression.indMatch (.varRef "c")
  [("Red", [], .intLit 0), ("Red", [], .intLit 1), ("Blue", [], .intLit 2)]).infer types ctx == none
#guard (Expression.indMatch (.varRef "c")
  [("Red", [], .intLit 0), ("Green", [], .intLit 1), ("Blue", [], .intLit 2),
    ("Blue", [], .intLit 3)]).infer types ctx == none
#guard (Expression.indMatch (.varRef "c")
  [("Red", [], .intLit 0), ("Green", [], .intLit 1), ("Blue", [], .intLit 2),
    ("Purple", [], .intLit 3)]).infer types ctx == none
#guard (Expression.indMatch (.varRef "c") []).infer types ctx == none

-- One name per thing the constructor carries, no more and no fewer.
#guard (Expression.indMatch (.varRef "sh")
  [("Circle", [], .intLit 0), ("Rect", ["w", "h"], .varRef "w"),
    ("At", ["q"], .intLit 0)]).infer types ctx == none
#guard (Expression.indMatch (.varRef "sh")
  [("Circle", ["r", "r'"], .varRef "r"), ("Rect", ["w", "h"], .varRef "w"),
    ("At", ["q"], .intLit 0)]).infer types ctx == none

-- The names are bound at the types their constructor declares, and at nothing else.
#guard (Expression.indMatch (.varRef "sh")
  [("Circle", ["r"], .plus (.varRef "r") (.intLit 1)), ("Rect", ["w", "h"], .varRef "w"),
    ("At", ["q"], .intLit 0)]).infer types ctx == some .int
#guard (Expression.indMatch (.varRef "sh")
  [("Circle", ["r"], .listReverse (.varRef "r")), ("Rect", ["w", "h"], .varRef "w"),
    ("At", ["q"], .intLit 0)]).infer types ctx == none
#guard (Expression.indMatch (.varRef "sh")
  [("Circle", ["r"], .intLit 0), ("Rect", ["w", "h"], .intLit 0),
    ("At", ["q"], .structGet (.varRef "q") "z")]).infer types ctx == none

-- They are in scope in their own alternative and nowhere else, and they shadow the enclosing
-- context the way a `lam`'s parameters do.
#guard (Expression.indMatch (.varRef "sh")
  [("Circle", ["r"], .intLit 0), ("Rect", ["w", "h"], .varRef "r"),
    ("At", ["q"], .intLit 0)]).infer types ctx == none
#guard (Expression.indMatch (.varRef "sh")
  [("Circle", ["n"], .plus (.varRef "n") (.varRef "n")), ("Rect", ["w", "h"], .varRef "w"),
    ("At", ["q"], .intLit 0)]).infer types ctx == some .int
#guard (Expression.indMatch (.varRef "sh")
  [("Circle", ["s"], .plus (.varRef "s") (.intLit 1)), ("Rect", ["w", "h"], .varRef "w"),
    ("At", ["q"], .intLit 0)]).infer types ctx == some .int

-- Every alternative has to produce the same type, because the match has one type however the value
-- it took apart was built.
#guard (Expression.indMatch (.varRef "c")
  [("Red", [], .intLit 0), ("Green", [], .stringLit "g"),
    ("Blue", [], .intLit 2)]).infer types ctx == none
#guard (Expression.indMatch (.varRef "c")
  [("Red", [], .varRef "nope"), ("Green", [], .intLit 1),
    ("Blue", [], .intLit 2)]).infer types ctx == none

-- Only a value of a declared inductive type can be taken apart, and the alternatives are the
-- constructors of *its* declaration.
#guard (Expression.indMatch (.varRef "n") [("Red", [], .intLit 0)]).infer types ctx == none
#guard (Expression.indMatch (.varRef "p") [("Red", [], .intLit 0)]).infer types ctx == none
#guard (Expression.indMatch (.varRef "nope") [("Red", [], .intLit 0)]).infer types ctx == none
#guard (Expression.indMatch (.varRef "c")
  [("Red", [], .intLit 0), ("Green", [], .intLit 1), ("Blue", [], .intLit 2)]).infer {} ctx == none

-- A match is an expression like any other: it can be built out of one and read out of one, and its
-- scrutinee can be anything of the right type.
#guard (Expression.plus (.indMatch (.indNew "Color" "Red" [])
  [("Red", [], .intLit 0), ("Green", [], .intLit 1), ("Blue", [], .intLit 2)])
  (.intLit 1)).infer types ctx == some .int
#guard (Expression.indMatch (.varRef "c")
  [("Red", [], .indNew "Shape" "Circle" [.intLit 1]),
    ("Green", [], .indNew "Shape" "Rect" [.intLit 1, .intLit 2]),
    ("Blue", [], .varRef "sh")]).infer types ctx == some (.ind "Shape")

/-- `fun (s : Shape) => match s with | Circle(r) => r + r | Rect(w, h) => w + h | At(q) => q.x` -/
private def size : FuncDecl where
  docstring := "How big `s` is, for a rough enough notion of size."
  name := "size"
  parameters := [("s", .ind "Shape")]
  body := .indMatch (.varRef "s")
    [("Circle", ["r"], .plus (.varRef "r") (.varRef "r")),
      ("Rect", ["w", "h"], .plus (.varRef "w") (.varRef "h")),
      ("At", ["q"], .structGet (.varRef "q") "x")]
  resultType := .int

-- A declaration takes and returns an inductive type like any other type, and it is the inductive
-- table that has to supply the declaration its parameter names — `At` also needs the struct table,
-- so `size` checks only against the bundle holding both.
#guard size.check types []
#guard !size.check {} []
#guard !size.check { is := Inductives.ofDecls [color, shape, tree] } []
#guard !({ size with resultType := .string } : FuncDecl).check types []

-- The same declaration with its alternatives written in another order is the same declaration as far
-- as checking is concerned, and one of them left out is still not.
#guard ({ size with body := (Expression.indMatch (.varRef "s")
  [("At", ["q"], .structGet (.varRef "q") "x"),
    ("Rect", ["w", "h"], .plus (.varRef "w") (.varRef "h")),
    ("Circle", ["r"], .plus (.varRef "r") (.varRef "r"))]) } : FuncDecl).check types []
#guard !({ size with body := (Expression.indMatch (.varRef "s")
  [("At", ["q"], .structGet (.varRef "q") "x"),
    ("Circle", ["r"], .plus (.varRef "r") (.varRef "r"))]) } : FuncDecl).check types []

/-- `fun (n : int) => Shape.Rect(n, n)` -/
private def square : FuncDecl where
  docstring := "A square of side `n`."
  name := "square"
  parameters := [("n", .int)]
  body := .indNew "Shape" "Rect" [.varRef "n", .varRef "n"]
  resultType := .ind "Shape"

#guard square.check types []
#guard !square.check {} []
#guard !({ square with resultType := .ind "Color" } : FuncDecl).check types []

/-! ### Distinct constructor names

What `InductiveDecl.CtorNamesUnique` asks of a declaration, and what a declaration failing it looks
like.  It is a condition on the declaration rather than something the checker enforces, exactly as
the uniqueness conditions on a `Program` are: expressions over `twoReds` below check as they would
over any other type, and what the repeated name costs is written out under it. -/

example : color.CtorNamesUnique := by decide
example : shape.CtorNamesUnique := by decide
example : tree.CtorNamesUnique := by decide

-- Which is what makes every constructor reachable: being one of the declaration's constructors is
-- enough to be the one its own name resolves to, at the data types written for it.
example : shape.constructors.lookup "Rect" = some [.int, .int] :=
  shape.lookup_ctor_self (by simp [InductiveDecl.CtorNamesUnique, shape]) (by simp [shape])

/-- Two constructors under one name, which is what the condition rules out. -/
private def twoReds : InductiveDecl where
  name := "TwoReds"
  constructors := [("Red", []), ("Red", [.int])]

example : ¬ twoReds.CtorNamesUnique := by decide

private def twoRedTypes : TypeDecls := { is := Inductives.ofDecls [twoReds] }

-- The second `Red` is unreachable: every rule about a constructor resolves it with `List.lookup`,
-- which stops at the first, so the data types the second declares are types nothing can build a
-- value at.
#guard (Expression.indNew "TwoReds" "Red" []).infer twoRedTypes [] == some (.ind "TwoReds")
#guard (Expression.indNew "TwoReds" "Red" [.intLit 1]).infer twoRedTypes [] == none

-- And exhaustiveness counts it all the same, so a match has to write a second alternative for it —
-- one checked against the first `Red`'s data types, and one `Eval` can never reach.
#guard (Expression.indMatch (.indNew "TwoReds" "Red" [])
  [("Red", [], .intLit 0)]).infer twoRedTypes [] == none
#guard (Expression.indMatch (.indNew "TwoReds" "Red" [])
  [("Red", [], .intLit 0), ("Red", [], .intLit 1)]).infer twoRedTypes [] == some .int
#guard (Expression.indMatch (.indNew "TwoReds" "Red" [])
  [("Red", [], .intLit 0), ("Red", ["n"], .varRef "n")]).infer twoRedTypes [] == none

-- Over a declaration that does satisfy the condition, an exhaustive match names each constructor
-- once, so there is no alternative `Eval` cannot reach.
example {alts : List (CtorName × List String × Expression)}
    (h : Expression.altsExhaustive shape.constructors alts = true) : (alts.map Prod.fst).Nodup :=
  Expression.alts_nodup_of_altsExhaustive (by decide) h

end Tests
