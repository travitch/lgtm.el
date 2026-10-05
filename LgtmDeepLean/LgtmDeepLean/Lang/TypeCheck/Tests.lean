module

import LgtmDeepLean.Lang.TypeCheck
meta import LgtmDeepLean.Lang.TypeCheck

/-! # Tests for the type checker

What `Expression.infer`, `FuncDecl.check`, and `Program.check` accept and turn down, worked over a
fixed table of struct and inductive declarations: each type former in turn, the uniqueness
conditions on the names a program declares, and `TypeDecls.budget` at its boundary. -/

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

/-- A struct with a field of function type, which is the one thing a structural comparison cannot
reach the bottom of. -/
private def withFn : StructDecl where
  name := "WithFn"
  fields := [("label", .string), ("step", .fn [.int] .int)]

/-- An inductive type that reaches a function type through a struct rather than carrying one, which
is what makes `Ty.comparable` a question about the declarations a type leads to rather than about the
type as written. -/
private def holder : InductiveDecl where
  name := "Holder"
  constructors := [("Empty", []), ("Held", [.struct "WithFn"])]

private def types : TypeDecls :=
  { ss := Structs.ofDecls [point, box, withFn],
    is := Inductives.ofDecls [color, shape, tree, holder] }

private def ctx : Context :=
  [("xs", .list .int), ("n", .int), ("s", .string), ("f", .fn [.int, .string] .int),
    ("p", .struct "Point"), ("b", .struct "Box"), ("c", .ind "Color"), ("sh", .ind "Shape"),
    ("t", .ind "Tree"), ("flag", .bool), ("wf", .struct "WithFn"), ("hd", .ind "Holder"),
    ("o", .option .int), ("op", .option (.struct "Point")), ("ofn", .option (.fn [.int] .int))]

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

/-! ### Equality

Which types a comparison may be used at, which is `Ty.comparable`, and then what `equals` does with
it: one type between the two operands, and a `bool` out of it whatever that type was. -/

-- A function type is reachable from itself and from nothing else among the leaves, so those are
-- comparable and it is not.
#guard Ty.comparable types .int
#guard Ty.comparable types .bool
#guard Ty.comparable types .string
#guard !Ty.comparable types (.fn [.int] .int)
#guard !Ty.comparable types (.fn [] .int)

-- A list is comparable exactly when its elements are, however deeply nested.
#guard Ty.comparable types (.list .int)
#guard Ty.comparable types (.list (.list .string))
#guard !Ty.comparable types (.list (.fn [.int] .int))
#guard !Ty.comparable types (.list (.list (.fn [.int] .int)))

-- A named type is comparable when every type its declaration leads to is, which is why the
-- declarations have to be walked: `Box` carries a `Point`, and `Holder` reaches a function type
-- through a struct that carries one.
#guard Ty.comparable types (.struct "Point")
#guard Ty.comparable types (.struct "Box")
#guard Ty.comparable types (.ind "Color")
#guard Ty.comparable types (.ind "Shape")
#guard !Ty.comparable types (.struct "WithFn")
#guard !Ty.comparable types (.ind "Holder")
#guard !Ty.comparable types (.list (.struct "WithFn"))

-- A recursive type is comparable all the same: the cycle contributes no field type the walk has not
-- already seen, and a value of one is finite however deep the type is.
#guard Ty.comparable types (.ind "Tree")
#guard Ty.comparable types (.list (.ind "Tree"))

-- An undeclared name is a type nothing has a value of, so there is nothing to compare at it.
#guard !Ty.comparable types (.struct "Nope")
#guard !Ty.comparable types (.ind "Nope")
#guard !Ty.comparable ({} : TypeDecls) (.struct "Point")

/-! `TypeDecls.budget` at its boundary.  The tables below are the shapes the count has to be right
for: a chain of distinct names as long as the table itself, and a cycle, which is what the walk gives
up on rather than follows. -/

/-- Four structure types in a chain, the last of them carrying a function: the longest path of
distinct names a table of four can have. -/
private def chain : TypeDecls :=
  { ss := Structs.ofDecls
      [{ name := "C1", fields := [("n", .struct "C2")] },
        { name := "C2", fields := [("n", .struct "C3")] },
        { name := "C3", fields := [("n", .struct "C4")] },
        { name := "C4", fields := [("step", .fn [.int] .int)] }] }

#guard !Ty.comparable chain (.struct "C1")
#guard !Ty.comparable chain (.struct "C4")

/-- The same chain ending in a name the table does not declare, which takes one step more than the
one ending in a function type: the name has to be *reached* for its lookup to fail. -/
private def chainMissing : TypeDecls :=
  { ss := Structs.ofDecls
      [{ name := "C1", fields := [("n", .struct "C2")] },
        { name := "C2", fields := [("n", .struct "C3")] },
        { name := "C3", fields := [("n", .struct "C4")] },
        { name := "C4", fields := [("n", .struct "Missing")] }] }

#guard !Ty.comparable chainMissing (.struct "C1")

/-- Two structure types that carry each other, and one that carries itself alongside a function.

Mutual recursion is a cycle the way direct recursion is, so the first two are comparable; the third
is not, and it is not the cycle that decides it — a function type in the same declaration is found
before the walk has anywhere to go round to. -/
private def cycles : TypeDecls :=
  { ss := Structs.ofDecls
      [{ name := "A", fields := [("b", .struct "B")] },
        { name := "B", fields := [("a", .struct "A"), ("n", .int)] },
        { name := "R", fields := [("r", .struct "R"), ("step", .fn [] .int)] }] }

#guard Ty.comparable cycles (.struct "A")
#guard Ty.comparable cycles (.struct "B")
#guard !Ty.comparable cycles (.struct "R")

-- Two operands of one comparable type make a `bool`, whatever that type was.
#guard (Expression.equals (.intLit 1) (.intLit 2)).infer types ctx == some .bool
#guard (Expression.equals (.stringLit "a") (.varRef "s")).infer types ctx == some .bool
#guard (Expression.equals (.boolLit true) (.varRef "flag")).infer types ctx == some .bool
#guard (Expression.equals (.varRef "xs") (.lnil .int)).infer types ctx == some .bool
#guard (Expression.equals (.varRef "p") (.varRef "p")).infer types ctx == some .bool
#guard (Expression.equals (.varRef "b") (.varRef "b")).infer types ctx == some .bool
#guard (Expression.equals (.varRef "c") (.varRef "c")).infer types ctx == some .bool
#guard (Expression.equals (.varRef "t") (.varRef "t")).infer types ctx == some .bool
#guard (Expression.equals (.intLit 1) (.intLit 2)).infer {} [] == some .bool

-- The type is read off the left operand and then required of the right, so operands of different
-- types have nothing to compare.
#guard (Expression.equals (.intLit 1) (.stringLit "a")).infer types ctx == none
#guard (Expression.equals (.varRef "n") (.varRef "flag")).infer types ctx == none
#guard (Expression.equals (.varRef "xs") (.varRef "n")).infer types ctx == none
#guard (Expression.equals (.lnil .int) (.lnil .string)).infer types ctx == none
#guard (Expression.equals (.varRef "p") (.varRef "b")).infer types ctx == none
#guard (Expression.equals (.varRef "c") (.varRef "sh")).infer types ctx == none

-- An ill-typed operand on either side makes the comparison ill typed.
#guard (Expression.equals (.varRef "nope") (.intLit 1)).infer types ctx == none
#guard (Expression.equals (.intLit 1) (.varRef "nope")).infer types ctx == none
#guard (Expression.equals (.plus (.intLit 1) (.stringLit "a")) (.intLit 1)).infer types ctx == none

-- And operands of a type a comparison cannot reach the bottom of are rejected, however the function
-- type is arrived at: directly, under a list, or through a declaration.
#guard (Expression.equals (.varRef "f") (.varRef "f")).infer types ctx == none
#guard (Expression.equals (.lam [("x", .int)] (.varRef "x"))
  (.lam [("x", .int)] (.varRef "x"))).infer types ctx == none
#guard (Expression.equals (.lnil (.fn [.int] .int)) (.lnil (.fn [.int] .int))).infer types ctx
  == none
#guard (Expression.equals (.varRef "wf") (.varRef "wf")).infer types ctx == none
#guard (Expression.equals (.varRef "hd") (.varRef "hd")).infer types ctx == none

-- A struct type whose declaration the table does not have is no more comparable than the comparison
-- is typeable without it.
#guard (Expression.equals (.varRef "p") (.varRef "p")).infer {} ctx == none

-- A comparison is an expression like any other: it goes where a `bool` goes, and its operands are
-- whatever has the type they share.
#guard (Expression.ite (.equals (.varRef "n") (.intLit 1)) (.intLit 1) (.intLit 2)).infer types ctx
  == some .int
#guard (Expression.equals (.equals (.varRef "n") (.intLit 1)) (.varRef "flag")).infer types ctx
  == some .bool
#guard (Expression.equals (.plus (.varRef "n") (.intLit 1)) (.varRef "n")).infer types ctx
  == some .bool
#guard (Expression.equals (.structGet (.varRef "p") "x") (.intLit 0)).infer types ctx == some .bool
#guard (Expression.equals (.lcons (.intLit 1) (.varRef "xs")) (.varRef "xs")).infer types ctx
  == some .bool
#guard (Expression.lam [("q", .ind "Tree")] (.equals (.varRef "q") (.varRef "t"))).infer types ctx
  == some (.fn [.ind "Tree"] .bool)
#guard (Expression.let_ "e" (.equals (.varRef "n") (.intLit 1)) (.varRef "e")).infer types ctx
  == some .bool

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


/-! ### Options

The option type is the one type former besides `list` that is structural rather than nominal, so
`types` has nothing to say about it: an `option` carries its element type, and a value of one is
either empty or holds a value of that type.  `ctx` gives `o` an `option int`, `op` an option of a
declared struct, and `ofn` one of function type — which is the one thing a comparison cannot reach
the bottom of, under an option as under a list. -/

-- An option type is the element type and nothing else, so two of them agree exactly when their
-- element types do, and an option is not the list of the same thing.
#guard Ty.option .int == Ty.option .int
#guard Ty.option .int != Ty.option .string
#guard Ty.option .int != Ty.list .int
#guard Ty.option (.option .int) == Ty.option (.option .int)
#guard Ty.option (.option .int) != Ty.option .int
#guard Ty.option (.struct "Point") != Ty.option (.struct "Pair")

-- An empty option takes its type from its annotation, the way an empty list does.
#guard (Expression.optionNone .int).infer types ctx == some (.option .int)
#guard (Expression.optionNone .string).infer types ctx == some (.option .string)
#guard (Expression.optionNone (.option .int)).infer types ctx == some (.option (.option .int))
#guard (Expression.optionNone (.list .int)).infer types ctx == some (.option (.list .int))
#guard (Expression.optionNone (.struct "Point")).infer types ctx == some (.option (.struct "Point"))

-- An annotation names a type rather than being checked against the table, so an undeclared name
-- goes through here exactly as it does under `lnil`: it is what *builds* a value of one that the
-- table is consulted for.
#guard (Expression.optionNone (.struct "Nope")).infer types ctx == some (.option (.struct "Nope"))

-- A `some` takes its type from the value it holds, so it needs no annotation.
#guard (Expression.optionSome (.intLit 1)).infer types ctx == some (.option .int)
#guard (Expression.optionSome (.varRef "s")).infer types ctx == some (.option .string)
#guard (Expression.optionSome (.varRef "p")).infer types ctx == some (.option (.struct "Point"))
#guard (Expression.optionSome (.varRef "f")).infer types ctx
  == some (.option (.fn [.int, .string] .int))
#guard (Expression.optionSome (.plus (.varRef "n") (.intLit 1))).infer types ctx
  == some (.option .int)

-- And an ill-typed value makes the whole thing ill typed.
#guard (Expression.optionSome (.varRef "nope")).infer types ctx == none
#guard (Expression.optionSome (.plus (.intLit 1) (.stringLit "a"))).infer types ctx == none

-- Options nest, in each other and in everything else: the type former is a type like any other.
#guard (Expression.optionSome (.optionSome (.intLit 1))).infer types ctx
  == some (.option (.option .int))
#guard (Expression.optionSome (.optionNone .int)).infer types ctx == some (.option (.option .int))
#guard (Expression.lcons (.varRef "o") (.lnil (.option .int))).infer types ctx
  == some (.list (.option .int))
#guard (Expression.lcons (.varRef "o") (.lnil (.option .string))).infer types ctx == none
#guard (Expression.optionSome (.varRef "xs")).infer types ctx == some (.option (.list .int))
#guard (Expression.lam [("y", .option .int)] (.varRef "y")).infer types ctx
  == some (.fn [.option .int] (.option .int))

-- An option is comparable exactly when what it holds is, which is the same walk a list gets.
#guard Ty.comparable types (.option .int)
#guard Ty.comparable types (.option (.list .string))
#guard Ty.comparable types (.option (.struct "Point"))
#guard Ty.comparable types (.option (.ind "Tree"))
#guard !Ty.comparable types (.option (.fn [.int] .int))
#guard !Ty.comparable types (.option (.struct "WithFn"))
#guard !Ty.comparable types (.list (.option (.fn [.int] .int)))
#guard (Expression.equals (.varRef "o") (.optionNone .int)).infer types ctx == some .bool
#guard (Expression.equals (.varRef "o") (.optionSome (.intLit 1))).infer types ctx == some .bool
#guard (Expression.equals (.varRef "o") (.optionSome (.stringLit "a"))).infer types ctx == none
#guard (Expression.equals (.varRef "ofn") (.varRef "ofn")).infer types ctx == none

-- A match gives the type its two cases agree on, with the name of the second bound to what the
-- option holds.
#guard (Expression.optionMatch (.varRef "o") (.intLit 0) "x" (.varRef "x")).infer types ctx
  == some .int
#guard (Expression.optionMatch (.varRef "o") (.intLit 0) "x"
  (.plus (.varRef "x") (.intLit 1))).infer types ctx == some .int
#guard (Expression.optionMatch (.varRef "o") (.boolLit false) "x"
  (.equals (.varRef "x") (.intLit 0))).infer types ctx == some .bool
#guard (Expression.optionMatch (.varRef "op") (.intLit 0) "q"
  (.structGet (.varRef "q") "x")).infer types ctx == some .int

-- The name is bound at the type the scrutinee's option holds, so using it at another type is ill
-- typed, and it is in scope in the second case alone.
#guard (Expression.optionMatch (.varRef "o") (.intLit 0) "x"
  (.plus (.varRef "x") (.stringLit "a"))).infer types ctx == none
#guard (Expression.optionMatch (.varRef "op") (.intLit 0) "q" (.varRef "q")).infer types ctx == none
#guard (Expression.optionMatch (.varRef "o") (.varRef "x") "x" (.varRef "x")).infer types ctx
  == none

-- It shadows an enclosing binding of the same name, the way a `let`'s does, and only inside its own
-- case: the first case still sees the outer `n`.
#guard (Expression.optionMatch (.optionSome (.stringLit "a")) (.stringLit "b") "n"
  (.varRef "n")).infer types ctx == some .string
#guard (Expression.optionMatch (.optionSome (.stringLit "a")) (.varRef "n") "n"
  (.varRef "n")).infer types ctx == none

-- Both cases are held to one type, which is what makes the form have a type at all: neither the
-- value nor the scrutinee says which case will run.
#guard (Expression.optionMatch (.varRef "o") (.intLit 0) "x" (.stringLit "a")).infer types ctx
  == none
#guard (Expression.optionMatch (.varRef "o") (.stringLit "a") "x" (.varRef "x")).infer types ctx
  == none

-- The scrutinee has to be an option, and nothing else will do: there is no value of another type
-- for the two cases to be a case analysis of.
#guard (Expression.optionMatch (.varRef "n") (.intLit 0) "x" (.varRef "x")).infer types ctx == none
#guard (Expression.optionMatch (.varRef "xs") (.intLit 0) "x" (.varRef "x")).infer types ctx == none
#guard (Expression.optionMatch (.varRef "c") (.intLit 0) "x" (.varRef "x")).infer types ctx == none
#guard (Expression.optionMatch (.varRef "nope") (.intLit 0) "x" (.varRef "x")).infer types ctx
  == none

-- An ill-typed case on either side makes the match ill typed, however the other one goes.
#guard (Expression.optionMatch (.varRef "o") (.varRef "nope") "x" (.varRef "x")).infer types ctx
  == none
#guard (Expression.optionMatch (.varRef "o") (.intLit 0) "x" (.varRef "nope")).infer types ctx
  == none

-- A match on an option of options is a match whose bound name is itself an option, which is all
-- nesting comes to.
#guard (Expression.optionMatch (.optionSome (.optionSome (.intLit 1))) (.optionNone .int) "x"
  (.varRef "x")).infer types ctx == some (.option .int)

-- A match is an expression like any other: it goes where its type goes, and it is an operand of
-- whatever that type is an operand of.
#guard (Expression.plus (.optionMatch (.varRef "o") (.intLit 0) "x" (.varRef "x"))
  (.intLit 1)).infer types ctx == some .int
#guard (Expression.optionSome (.optionMatch (.varRef "o") (.intLit 0) "x"
  (.varRef "x"))).infer types ctx == some (.option .int)

/-- `fun (o : option int) => match o with | none => 0 | some(x) => x + 1` -/
private def succOr : FuncDecl where
  docstring := "One more than what `o` holds, and `0` when it holds nothing."
  name := "succ-or"
  parameters := [("o", .option .int)]
  body := .optionMatch (.varRef "o") (.intLit 0) "x" (.plus (.varRef "x") (.intLit 1))
  resultType := .int

-- A declaration over the new forms checks like any other, and against no table at all: an option
-- names nothing for a `TypeDecls` to resolve.
#guard succOr.check {} []
#guard !({ succOr with resultType := .option .int } : FuncDecl).check {} []
#guard !({ succOr with parameters := [("o", .int)] } : FuncDecl).check {} []
#guard !({ succOr with parameters := [("o", .option .string)] } : FuncDecl).check {} []

/-- `fun (n : int) => some(n)` -/
private def justIt : FuncDecl where
  docstring := "`n`, held in an option."
  name := "just-it"
  parameters := [("n", .int)]
  body := .optionSome (.varRef "n")
  resultType := .option .int

#guard justIt.check {} []
#guard !({ justIt with resultType := .option .string } : FuncDecl).check {} []
#guard !({ justIt with resultType := .int } : FuncDecl).check {} []

/-- `fun => none : int`, which is the shortest declaration that returns an option: the annotation is
the only thing that says which one. -/
private def nothing : FuncDecl where
  docstring := "Nothing, at `int`."
  name := "nothing"
  parameters := []
  body := .optionNone .int
  resultType := .option .int

#guard nothing.check {} []
#guard !({ nothing with resultType := .option .string } : FuncDecl).check {} []
#guard !({ nothing with body := Expression.optionNone .string } : FuncDecl).check {} []

-- Checking agrees with inference on the new forms too.
#guard (Expression.optionNone .int).check types ctx (.option .int)
#guard !(Expression.optionNone .int).check types ctx (.option .string)
#guard !(Expression.optionNone .int).check types ctx .int
#guard (Expression.optionSome (.intLit 1)).check types ctx (.option .int)
#guard !(Expression.optionSome (.intLit 1)).check types ctx .int
#guard (Expression.optionMatch (.varRef "o") (.intLit 0) "x" (.varRef "x")).check types ctx .int
