module

public import LgtmDeepLean.Lang.IR
public import LgtmDeepLean.Lang.TypeCheck.TypeDecls

/-! # Comparable types

What `Expression.equals` may be used at.  A deep structural comparison has to reach every value the
values it is given are made of, and a closure is the one thing it can say nothing about: two
functions are the same function when they agree on every argument, which is not something either
value carries.  So `equals` is restricted to the types no function type is reachable from, and this
is where that is decided.

*Reachable* rather than mentioned, because a struct and an inductive type are only names: a `Point`
says nothing about its fields until `td.ss` resolves it, so deciding this means walking the
declarations a type leads to, and that walk has to be made finite.  A recursive type is why: `Tree
{ Leaf, Node(Tree, Tree) }` leads to itself, so a walk that followed every name it met would never
be done.  What bounds it is a budget of name steps, spent one per declaration opened and generous
enough that running out means a name has been met twice — a cycle, which contributes no type the walk
has not already seen, so `true` is the answer there.  `TypeDecls.budget` is where the size of it is
argued.

A module of its own because it is the one condition in the checker that is not about an expression
at all: `Expression.infer` asks it about a single form, and the answer is settled by the type
declarations a program wrote down before any expression is looked at.

The definitions are exposed, for the reason `Expression.altsExhaustive` is: a proof that a
declaration checks is left with one of these on a type and a table a program wrote out, and has to be
able to see through it. -/

/-- The names of every type `td` declares.  There are as many names a walk can meet as there are
entries here, which is what `TypeDecls.budget` is counted from. -/
@[expose] public def TypeDecls.names (td : TypeDecls) : List String :=
  td.ss.map Prod.fst ++ td.is.map Prod.fst

/-- How many declarations a comparability walk may open before it gives up and says `true`.

One per name `td` declares, and one more.  That is enough to be sure that giving up is only ever a
cycle: a function type reachable from a type is reachable by following *distinct* names — a path that
repeats one can have the loop cut out of it and still arrive — so it is reachable within one step per
declared name.  The extra step is for the name at the end of such a path being one `td` does not
declare, which is a reason to say `false` and so has to be reached rather than assumed.

A walk that still has budget when it meets a name it has already met is doing the same work twice and
answering the same thing, so it costs nothing but time; a walk that runs out has gone deeper than any
path of distinct names could, and the shorter path it is the loopy version of was walked as well. -/
@[expose] public def TypeDecls.budget (td : TypeDecls) : Nat := td.names.length + 1

/-- Is no function type reachable from `t`, with `sOk` and `iOk` deciding that for the structure and
inductive names `t` mentions?

The whole of the type side of comparability: the three leaves are comparable, a function type is not,
a list is comparable exactly when its elements are, and a named type is whatever the oracle for its
kind says.  Two oracles rather than one because `td` has two tables: a name may be both a structure
type and an inductive type, and `Ty.struct` and `Ty.ind` resolve in different places.

Leaving the names to an oracle is what keeps this recursion on `t` alone, which is what makes it
compute: `TypeDecls.structComparable` is the oracle, and it spends the budget. -/
@[expose] public def Ty.comparableWith (sOk iOk : String → Bool) : Ty → Bool
  | .bool | .int | .string => true
  | .fn _ _ => false
  | .list t => Ty.comparableWith sOk iOk t
  | .struct name => sOk name
  | .ind name => iOk name

mutual

/-- Is no function type reachable from the structure type `name`, within `n` further declarations?

The declaration has to be there — an undeclared name is a type nothing has a value of, so there is
nothing to compare at it — and every type it gives a field has to be comparable, with the names *they*
mention decided one step further down.

`n = 0` is the budget running out, and the answer there is `true`: by then the walk is deeper than any
path of distinct names, so it is going round a cycle, and a cycle adds nothing a shallower walk did
not already see.  `TypeDecls.budget` is what makes that the only way to reach it. -/
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

/-- Can two values of type `t` be compared?  Which is to say: is no function type reachable from `t`
among the types `td` declares. -/
@[expose] public def Ty.comparable (td : TypeDecls) (t : Ty) : Bool :=
  Ty.comparableWith (td.structComparable td.budget) (td.indComparable td.budget) t

/-! What `Ty.comparable` comes to at each type former, which is what a proof that a declaration
checks is left with.  The three leaves, a function type and a list need nothing of the tables and so
are settled here once; a named type is the walk itself, and a proof meeting one of those computes
`Ty.comparable` on the table its program wrote out — which `decide` is enough for. -/

@[simp, grind =] public theorem Ty.comparable_bool {td : TypeDecls} :
    Ty.comparable td .bool = true := rfl

@[simp, grind =] public theorem Ty.comparable_int {td : TypeDecls} :
    Ty.comparable td .int = true := rfl

@[simp, grind =] public theorem Ty.comparable_string {td : TypeDecls} :
    Ty.comparable td .string = true := rfl

/-- A function type is the one thing a structural comparison cannot reach the bottom of, which is the
whole reason this condition exists. -/
@[simp, grind =] public theorem Ty.comparable_fn {td : TypeDecls} {ps : List Ty} {r : Ty} :
    Ty.comparable td (.fn ps r) = false := rfl

/-- A list is comparable exactly when its elements are: comparing two of them compares the elements,
so a list of functions is no more comparable than a function is. -/
@[simp, grind =] public theorem Ty.comparable_list {td : TypeDecls} {t : Ty} :
    Ty.comparable td (.list t) = Ty.comparable td t := rfl
