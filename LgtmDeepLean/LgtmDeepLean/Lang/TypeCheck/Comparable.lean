module

public import LgtmDeepLean.Lang.IR
public import LgtmDeepLean.Lang.TypeCheck.TypeDecls

/-! # Comparable types

This module defines what types the two polymorphic comparisons can be applied to: equality
(`Expression.equals`), which is `Ty.comparable`, and ordering (`Expression.lt` and
`Expression.le`), which is `Ty.orderable`.

Any type that is not and does not contain a function type or a hashmap type can be compared for
equality.

The general strategy is to use depth-first search over all types transitively referenced by
the type under consideration.  Lean requires that recursion is bounded.  We use the number of
defined types as the recursion bound for each depth-first search.

Ordering needs none of that machinery, and the second half of this module says why: it accepts no
type that names a declaration, so nothing is ever looked up and there is no cycle to bound.

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
  | .except e t => Ty.comparableWith sOk iOk e && Ty.comparableWith sOk iOk t
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

/-- And an except exactly when both halves are: a comparison of two of them that agree about which
half they carry is a comparison of the values they carry there, so either half is one it may have to
reach the bottom of.

Both rather than one, which is where this parts company with `option`: an error carries a value of
its own, so there is no half a comparison is sure not to be handed. -/
@[simp, grind =] public theorem Ty.comparable_except {td : TypeDecls} {e t : Ty} :
    Ty.comparable td (.except e t) = (Ty.comparable td e && Ty.comparable td t) := rfl

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

/-! ## Ordered types

Which types `Expression.lt` and `Expression.le` can be applied to, the way `Ty.comparable` is which
types `Expression.equals` can be.

It takes no `TypeDecls`, and that is the whole difference between the two.  An ordering is given on
`int` and `string` and carried through `option`, `list` and `tuple`, none of which names a
declaration, so there is nothing to look up, nothing to be missing, and no cycle for a budget to cut
off.  A `struct` or an `ind` is not ordered at all rather than ordered when the types it leads to
are: a declaration's fields are named rather than positional, so there is nothing to say which of
them an ordering should look at first, and a constructor's place in an ordering would be its place in
a list of constructors — neither is an order the declaration meant. -/

mutual

/-- Is `t` a type with an ordering: `int` or `string`, or an `option`, `list` or `tuple` of types
that are?

`bool` is turned down with the nominal types.  `false < true` is an ordering nobody would argue
with, but a `bool` is what a comparison *produces* here rather than something it is given, so there
is nothing an ordering on it would be for.  A hashmap is turned down for the reason `Ty.comparable`
turns it down — the order its bindings are carried in is not canonical, so no comparison of two maps
answers about the maps — and a function type for the reason that one turns it down.  An except is
turned down for a reason of its own: see `Ty.orderable_except`. -/
@[expose] public def Ty.orderable : Ty → Bool
  | .int | .string => true
  | .option t => Ty.orderable t
  | .list t => Ty.orderable t
  | .tuple ts => Ty.orderableList ts
  | .bool | .fn _ _ | .hashmap _ _ | .except _ _ | .struct _ | .ind _ => false

/-- The same question of every type in a list: the types a `tuple` holds, each of which a
lexicographic comparison may have to reach before it has an answer.

`Ty.orderable` run along a list and nothing more, which is a second function for the reason
`Ty.beqList` is one beside `Ty.beq`: a `Ty` carries a `List Ty` at `tuple`, so the walk over the
list is what the recursion there goes through. -/
@[expose] public def Ty.orderableList : List Ty → Bool
  | [] => true
  | t :: ts => Ty.orderable t && Ty.orderableList ts

end

@[simp] public theorem Ty.orderableList_eq_all {ts : List Ty} :
    Ty.orderableList ts = ts.all Ty.orderable := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [Ty.orderableList, ih]

/-! What `Ty.orderable` comes to at each type former, which is what a proof elsewhere reads it
through.  All but the tuple case are the definition's own equations; they are stated here so that
`simp` and `grind` have them without being handed the definition. -/

@[simp, grind =] public theorem Ty.orderable_int : Ty.orderable .int = true := rfl

@[simp, grind =] public theorem Ty.orderable_string : Ty.orderable .string = true := rfl

/-- A `bool` is ordered by nothing here: it is what a comparison produces, not what one compares. -/
@[simp, grind =] public theorem Ty.orderable_bool : Ty.orderable .bool = false := rfl

@[simp, grind =] public theorem Ty.orderable_fn {ps : List Ty} {r : Ty} :
    Ty.orderable (.fn ps r) = false := rfl

@[simp, grind =] public theorem Ty.orderable_hashmap {kt vt : Ty} :
    Ty.orderable (.hashmap kt vt) = false := rfl

/-- An except is ordered by nothing, whatever the two types it relates are, where an option of them
would be: an empty option comes before one that holds a value because there is one thing an option
can hold and either there is one or there is not, while an error and a success carry values of two
unrelated types — so neither "an error comes first" nor the reverse is an ordering the type
suggests, and Lean's own `Except` is given no `Ord` either. -/
@[simp, grind =] public theorem Ty.orderable_except {e t : Ty} :
    Ty.orderable (.except e t) = false := rfl

/-- A declared type is turned down whatever it declares, which is where this parts company with
`Ty.comparable`: there is no walk over the declarations, because no ordering is being claimed for
one. -/
@[simp, grind =] public theorem Ty.orderable_struct {name : String} :
    Ty.orderable (.struct name) = false := rfl

@[simp, grind =] public theorem Ty.orderable_ind {name : String} :
    Ty.orderable (.ind name) = false := rfl

/-- An option is ordered exactly when the type it holds is: the empty one comes first, and the rest
is a comparison of the values two of them hold. -/
@[simp, grind =] public theorem Ty.orderable_option {t : Ty} :
    Ty.orderable (.option t) = Ty.orderable t := rfl

/-- A list is ordered exactly when its elements are, lexicographically. -/
@[simp, grind =] public theorem Ty.orderable_list {t : Ty} :
    Ty.orderable (.list t) = Ty.orderable t := rfl

/-- And a tuple exactly when every type it holds is, which is the list case read positionally: a
lexicographic comparison stops at the first position the two disagree at, and any position may be
that one. -/
@[simp, grind =] public theorem Ty.orderable_tuple {ts : List Ty} :
    Ty.orderable (.tuple ts) = ts.all Ty.orderable := by
  rw [Ty.orderable, Ty.orderableList_eq_all]
