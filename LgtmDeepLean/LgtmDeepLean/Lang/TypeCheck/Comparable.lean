module

public import LgtmDeepLean.Lang.IR
public import LgtmDeepLean.Lang.TypeCheck.TypeDecls

/-! # Comparable types

This module defines what types polymorphic equality (`Expression.equals`) can be applied to.
Any type that is not or does not contain a function type can be compared for equality.

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

/-- Is no function type reachable from `t`, with `sOk` and `iOk` deciding that for the structure and
inductive names `t` mentions?

Leaving the decision on structure and inductive types to the `sOk` and `iOk` oracles instead of
directly computing them from `TypeDecls` is helpful to avoid sinking this into the mutual block and
to keep the termination checking simple. -/
@[expose] public def Ty.comparableWith (sOk iOk : String → Bool) : Ty → Bool
  | .bool | .int | .string => true
  | .fn _ _ => false
  | .list t => Ty.comparableWith sOk iOk t
  | .struct name => sOk name
  | .ind name => iOk name

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

/-- Function types are the only thing that is currently not comparable. -/
@[simp, grind =] public theorem Ty.comparable_fn {td : TypeDecls} {ps : List Ty} {r : Ty} :
    Ty.comparable td (.fn ps r) = false := rfl

/-- A list is comparable exactly when its elements are. -/
@[simp, grind =] public theorem Ty.comparable_list {td : TypeDecls} {t : Ty} :
    Ty.comparable td (.list t) = Ty.comparable td t := rfl
