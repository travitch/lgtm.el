module

public import LgtmDeepLean.Lang.TypeCheck.TypeDecls

/-! # Uniqueness

This module defines infrastructure for stating and checking the required uniqueness properties
for well-formed programs:

- Functions/globals must have unique names
- Structure fields must have unique names within a single structure
- Inductive constructors must have unique names within a single inductive
- Structures must have unique names within a program
- Inductives must have unique names within a program.

-/

/-- With no two entries sharing a key, every entry of an association list is the one its own key
resolves to.

The converse of `List.mem_of_lookup`, and the direction that needs the keys to be distinct: a
repeated key is resolved to its leftmost entry, so nothing further along is reachable at all.
`List.lookup_keyed_self` is the same fact for a list keyed by a function, which is how a table
of declarations is built; this is for one that is already a list of pairs, which is what an
inductive declaration's constructors are. -/
private theorem List.lookup_of_mem {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)}
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
private theorem List.lookup_keyed_self {α β : Type} [BEq α] [LawfulBEq α] {f : β → α} {bs : List β}
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

/-- With no repeated names, `Globals.ofDecls` resolves every declaration to itself. -/
private theorem Globals.lookup_ofDecls_self {ds : List FuncDecl} (hu : (ds.map FuncDecl.name).Nodup)
    {d : FuncDecl} (hd : d ∈ ds) : (Globals.ofDecls ds).lookup d.name = some d := by
  simpa [Globals.ofDecls] using List.lookup_keyed_self hu hd

/-- With no repeated names, `Structs.ofDecls` resolves every structure declaration to itself.  This
is what `Program.StructNamesUnique` buys, exactly as `Globals.lookup_ofDecls_self` is what
`Program.NamesUnique` buys. -/
private theorem Structs.lookup_ofDecls_self {sds : List StructDecl}
    (hu : (sds.map StructDecl.name).Nodup) {sd : StructDecl} (hd : sd ∈ sds) :
    (Structs.ofDecls sds).lookup sd.name = some sd := by
  simpa [Structs.ofDecls] using List.lookup_keyed_self hu hd

/-- With no repeated names, `Inductives.ofDecls` resolves every inductive declaration to itself: the
same fact again, for the other table `Program.InductiveNamesUnique` is about. -/
private theorem Inductives.lookup_ofDecls_self {ids : List InductiveDecl}
    (hu : (ids.map InductiveDecl.name).Nodup) {d : InductiveDecl} (hd : d ∈ ids) :
    (Inductives.ofDecls ids).lookup d.name = some d := by
  simpa [Inductives.ofDecls] using List.lookup_keyed_self hu hd

/-- No two declarations share a name. -/
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

/-- No two structure declarations share a name. -/
@[expose] public def Program.StructNamesUnique (p : Program) : Prop :=
  (p.structDecls.map StructDecl.name).Nodup

public instance (p : Program) : Decidable p.StructNamesUnique :=
  inferInstanceAs (Decidable (p.structDecls.map StructDecl.name).Nodup)

/-- With no repeated names, every structure declaration in the program is the one its own name
resolves to. -/
public theorem Program.lookupStruct_self {p : Program} (hu : p.StructNamesUnique)
    {sd : StructDecl} (hd : sd ∈ p.structDecls) : p.lookupStruct sd.name = some sd :=
  Structs.lookup_ofDecls_self hu hd

/-- No two inductive declarations share a name. -/
@[expose] public def Program.InductiveNamesUnique (p : Program) : Prop :=
  (p.inductiveDecls.map InductiveDecl.name).Nodup

public instance (p : Program) : Decidable p.InductiveNamesUnique :=
  inferInstanceAs (Decidable (p.inductiveDecls.map InductiveDecl.name).Nodup)

/-- With no repeated names, every inductive declaration in the program is the one its own name
resolves to. -/
public theorem Program.lookupInductive_self {p : Program} (hu : p.InductiveNamesUnique)
    {d : InductiveDecl} (hd : d ∈ p.inductiveDecls) : p.lookupInductive d.name = some d :=
  Inductives.lookup_ofDecls_self hu hd

/-- `sd` has unique field names. [tag:struct_field_names_unique] -/
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

/-- `d` has unique constructor names [tag:inductive_constructor_names_unique]. -/
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
