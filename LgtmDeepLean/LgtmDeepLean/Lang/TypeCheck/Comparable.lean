module

public import LgtmDeepLean.Lang.IR
public import LgtmDeepLean.Lang.TypeCheck.TypeDecls

/-! # Comparable types

This module defines what types polymorphic equality (`Expression.equals`) can be applied to.
Any type that is not and does not contain a function type or a hashmap type can be compared for
equality.

The general strategy is to use depth-first search over all types transitively referenced by
the type under consideration.  Lean requires that recursion is bounded.  We use the number of
defined types as the recursion bound for each depth-first search.

 -/

/-- The names of every type `td` declares. -/
@[expose] public def TypeDecls.names (td : TypeDecls) : List String :=
  td.ss.map Prod.fst ++ td.is.map Prod.fst

/-- How many declarations a comparability walk may open before it gives up and says `true`.

One per name `td` declares, and one more.  That is enough to be sure that the search is only
forcibly terminated in the presence of a cycle, which remains sound. -/
@[expose] public def TypeDecls.budget (td : TypeDecls) : Nat := td.names.length + 1

mutual

/-- Is neither a function type nor a hashmap type reachable from `t`, with `sOk` and `iOk` deciding
that for the structure and inductive names `t` mentions?

Leaving the decision on structure and inductive types to the `sOk` and `iOk` oracles instead of
directly computing them from `TypeDecls` is helpful to avoid sinking this into the mutual block and
to keep the termination checking simple.  The one thing it is mutual with is
`Ty.comparableWithList`, which walks the types a `tuple` holds: a `Ty` carries a `List Ty` there, so
the walk over the list is a second function for the reason `Ty.beqList` is one beside `Ty.beq`.

A hashmap stops the walk the way a function type does, and for a reason of the same kind: a `Value`
of hashmap type is an association list, so two of them carry the bindings they were put in in the
order they were put in, and two maps binding the same keys to the same values are different lists
whenever they were built in different orders.  A structural comparison would therefore answer
something other than whether the two are the same map, which is the one thing `Expression.equals`
means — so a hashmap has no comparison rather than a misleading one.  Unlike a function type this
is a property of the representation rather than of the type, and it is the one thing here that a
canonical form for hashmap values would lift. -/
@[expose] public def Ty.comparableWith (sOk iOk : String → Bool) : Ty → Bool
  | .bool | .int | .string => true
  | .fn _ _ => false
  | .hashmap _ _ => false
  | .option t => Ty.comparableWith sOk iOk t
  | .list t => Ty.comparableWith sOk iOk t
  | .tuple ts => Ty.comparableWithList sOk iOk ts
  | .struct name => sOk name
  | .ind name => iOk name

/-- The same question of every type in a list: the types a `tuple` holds, each of which a comparison
of two tuples has to reach the bottom of.

A tuple is positional and its length is part of its type, so there is nothing here that a list's
element type does not already face — which is why this is `Ty.comparableWith` run along a list and
nothing more. -/
@[expose] public def Ty.comparableWithList (sOk iOk : String → Bool) : List Ty → Bool
  | [] => true
  | t :: ts => Ty.comparableWith sOk iOk t && Ty.comparableWithList sOk iOk ts

end

@[simp] public theorem Ty.comparableWithList_eq_all {sOk iOk : String → Bool} {ts : List Ty} :
    Ty.comparableWithList sOk iOk ts = ts.all (Ty.comparableWith sOk iOk) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [Ty.comparableWithList, ih]

mutual

/-- Is no function type reachable from the structure type `name`, within `n` further declarations?

When `n = 0`, the recursion budget has run out and the answer there is `true`.  By then the walk is
deeper than any path of distinct names, so it is in a cycle and a cycle adds nothing a shallower
walk did not already see. -/
@[expose] public def TypeDecls.structComparable (td : TypeDecls) : Nat → String → Bool
  | 0, _ => true
  | n + 1, name =>
    match td.ss.lookup name with
    | some sd =>
      sd.fields.all fun p =>
        Ty.comparableWith (td.structComparable n) (td.indComparable n) p.2
    | none => false

/-- The same question for an inductive type, which carries lists of data types rather than named
fields and is otherwise answered the same way. -/
@[expose] public def TypeDecls.indComparable (td : TypeDecls) : Nat → String → Bool
  | 0, _ => true
  | n + 1, name =>
    match td.is.lookup name with
    | some d =>
      d.constructors.all fun p =>
        p.2.all fun t => Ty.comparableWith (td.structComparable n) (td.indComparable n) t
    | none => false

end

/-- Test if two values of type `t` be compared.  The `TypeDecls` is required to provide
the context of how types referenced in `t` are defined. -/
@[expose] public def Ty.comparable (td : TypeDecls) (t : Ty) : Bool :=
  Ty.comparableWith (td.structComparable td.budget) (td.indComparable td.budget) t

@[simp, grind =] public theorem Ty.comparable_bool {td : TypeDecls} :
    Ty.comparable td .bool = true := rfl

@[simp, grind =] public theorem Ty.comparable_int {td : TypeDecls} :
    Ty.comparable td .int = true := rfl

@[simp, grind =] public theorem Ty.comparable_string {td : TypeDecls} :
    Ty.comparable td .string = true := rfl

/-- Function types and hashmap types are the two things that are currently not comparable. -/
@[simp, grind =] public theorem Ty.comparable_fn {td : TypeDecls} {ps : List Ty} {r : Ty} :
    Ty.comparable td (.fn ps r) = false := rfl

/-- A hashmap is not comparable whatever it holds, where a list of the same elements would be: it is
the association list a hashmap value is that has no canonical form, not the types it relates. -/
@[simp, grind =] public theorem Ty.comparable_hashmap {td : TypeDecls} {kt vt : Ty} :
    Ty.comparable td (.hashmap kt vt) = false := rfl

/-- A list is comparable exactly when its elements are. -/
@[simp, grind =] public theorem Ty.comparable_list {td : TypeDecls} {t : Ty} :
    Ty.comparable td (.list t) = Ty.comparable td t := rfl

/-- And an option exactly when the type it holds is, for the same reason: the only value of one that
a comparison has anything to look at is the value it holds. -/
@[simp, grind =] public theorem Ty.comparable_option {td : TypeDecls} {t : Ty} :
    Ty.comparable td (.option t) = Ty.comparable td t := rfl

/-- A tuple is comparable exactly when every type it holds is, which is the list case read
positionally: the two tuples a comparison is given are the same length — that is their type — so
every position is one it has to be able to reach the bottom of.

A hashmap type among them stops it, so `tuple [kt, vt]` — what `hashmapToList` produces a list of —
is comparable exactly when the map's two types are.  That is not the comparison on hashmaps arriving
by another route: what `Ty.comparable` turns a hashmap down for is the order its bindings are carried
in, and a list of tuples compared elementwise answers about that order rather than in spite of it. -/
@[simp, grind =] public theorem Ty.comparable_tuple {td : TypeDecls} {ts : List Ty} :
    Ty.comparable td (.tuple ts) = ts.all (Ty.comparable td) := by
  rw [Ty.comparable, Ty.comparableWith, Ty.comparableWithList_eq_all]
  rfl
