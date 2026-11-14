module

import LgtmDeepLean.Lang.TypeCheck
meta import LgtmDeepLean.Lang.TypeCheck

/-! # Tests for the type checker

What `Expression.infer`, `FuncDecl.check`, and `Program.check` accept and turn down, worked over a
fixed table of struct and inductive declarations: each type former in turn, the uniqueness
conditions on the names a program declares, and `TypeDecls.budget` at its boundary.  What a check
that did not pass *says* is the last section. -/

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
    ("o", .option .int), ("op", .option (.struct "Point")), ("ofn", .option (.fn [.int] .int)),
    ("m", .hashmap .string .int), ("mp", .hashmap .string (.struct "Point")),
    ("mfn", .hashmap .string (.fn [.int] .int)), ("mbad", .hashmap (.fn [.int] .int) .int),
    ("tu", .tuple [.string, .int]), ("tu3", .tuple [.int, .string, .bool]), ("tue", .tuple []),
    ("tufn", .tuple [.string, .fn [.int] .int])]

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

-- A minimum and a maximum ask what arithmetic asks and answer the same: two `int`s in, an `int`
-- out, and nothing else accepted on either side.
#guard (Expression.min (.varRef "n") (.intLit 1)).infer types ctx == some .int

#guard (Expression.max (.varRef "n") (.intLit 1)).infer types ctx == some .int

#guard
  (Expression.min (.max (.intLit 1) (.intLit 2)) (.plus (.varRef "n") (.intLit 3))).infer types
      ctx ==
    some .int

#guard (Expression.min (.varRef "s") (.intLit 1)).infer types ctx == none

#guard (Expression.max (.intLit 1) (.varRef "xs")).infer types ctx == none

#guard (Expression.min (.varRef "nope") (.intLit 1)).infer types ctx == none

-- Unlike `lt` and `le`, neither is polymorphic: an ordering a comparison reaches is still not one
-- either of these is given, because what comes back is an operand rather than a `bool`.
#guard (Expression.lt (.varRef "s") (.varRef "s")).infer types ctx == some .bool

#guard (Expression.min (.varRef "s") (.varRef "s")).infer types ctx == none

#guard (Expression.max (.varRef "xs") (.varRef "xs")).infer types ctx == none

-- An empty list takes its type from its annotation, not from its context.
#guard (Expression.lnil .int).infer types ctx == some (.list .int)

#guard (Expression.lnil (.list .int)).infer types ctx == some (.list (.list .int))

-- A non-empty list takes its element type from its head, and its tail has to agree.
#guard (Expression.lcons (.intLit 1) (.lnil .int)).infer types ctx == some (.list .int)

#guard (Expression.lcons (.intLit 1) (.varRef "xs")).infer types ctx == some (.list .int)

#guard
  (Expression.lcons (.varRef "xs") (.lnil (.list .int))).infer types ctx ==
    some (.list (.list .int))

#guard (Expression.lcons (.intLit 1) (.intLit 2)).infer types ctx == none

#guard (Expression.lcons (.intLit 1) (.lnil (.list .int))).infer types ctx == none

#guard (Expression.lcons (.varRef "xs") (.varRef "xs")).infer types ctx == none

-- Lists are homogeneous across the new type too, so a mixed list has no type.
#guard (Expression.lcons (.stringLit "a") (.lnil .string)).infer types ctx == some (.list .string)

#guard (Expression.lcons (.stringLit "a") (.lnil .int)).infer types ctx == none

#guard (Expression.lcons (.intLit 1) (.lnil .string)).infer types ctx == none

#guard (Expression.lcons (.stringLit "a") (.varRef "xs")).infer types ctx == none

-- A list of empty lists needs no expected type to be inferred, only agreeing annotations.
#guard
  (Expression.lcons (.lnil .int) (.lnil (.list .int))).infer types ctx == some (.list (.list .int))

#guard (Expression.lcons (.lnil .int) (.lnil .int)).infer types ctx == none

-- Reversing a list keeps its type, whatever the element type is.
#guard (Expression.listReverse (.varRef "xs")).infer types ctx == some (.list .int)

#guard (Expression.listReverse (.lnil .string)).infer types ctx == some (.list .string)

#guard
  (Expression.listReverse (.lcons (.intLit 1) (.lnil .int))).infer types ctx == some (.list .int)

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

-- A length is an `int` whatever the elements are: the element type is counted, not inspected.
#guard (Expression.listLength (.varRef "xs")).infer types ctx == some .int

#guard (Expression.listLength (.lnil .string)).infer types ctx == some .int

#guard (Expression.listLength (.lcons (.intLit 1) (.lnil .int))).infer types ctx == some .int

#guard (Expression.listLength (.lnil (.list .int))).infer types ctx == some .int

-- Only a list has a length, so a non-list operand is ill typed.
#guard (Expression.listLength (.intLit 1)).infer types ctx == none

#guard (Expression.listLength (.stringLit "a")).infer types ctx == none

#guard (Expression.listLength (.varRef "n")).infer types ctx == none

#guard (Expression.listLength (.varRef "f")).infer types ctx == none

-- An ill-typed operand makes the whole length ill typed.
#guard (Expression.listLength (.varRef "nope")).infer types ctx == none

#guard (Expression.listLength (.lcons (.intLit 1) (.lnil .string))).infer types ctx == none

-- A length composes with the `int` operations on the way out and with `reverse` on the way in,
-- but lengths do not nest: what one gives back is not a list.
#guard (Expression.plus (.listLength (.varRef "xs")) (.intLit 1)).infer types ctx == some .int

#guard (Expression.listLength (.listReverse (.varRef "xs"))).infer types ctx == some .int

#guard (Expression.listLength (.listLength (.varRef "xs"))).infer types ctx == none

-- A mapping takes its element type from what the function returns, which is the one list form whose
-- result is a list of something other than its operand's elements: `reverse` passes the type
-- through and `length` discards it, where this one replaces it.
#guard
  (Expression.listMap (.varRef "xs") (.lam [("x", .int)] (.varRef "x"))).infer types ctx ==
    some (.list .int)

#guard
  (Expression.listMap (.varRef "xs") (.lam [("x", .int)] (.plus (.varRef "x") (.intLit 1)))).infer
      types ctx ==
    some (.list .int)

#guard
  (Expression.listMap (.varRef "xs") (.lam [("x", .int)] (.stringLit "a"))).infer types ctx ==
    some (.list .string)

#guard
  (Expression.listMap (.varRef "xs") (.lam [("x", .int)] (.optionSome (.varRef "x")))).infer types
      ctx ==
    some (.list (.option .int))

#guard
  (Expression.listMap (.lnil (.struct "Point"))
          (.lam [("p", .struct "Point")] (.structGet (.varRef "p") "x"))).infer
      types ctx ==
    some (.list .int)

-- The function takes one parameter, at the list's element type: one of the wrong arity or at the
-- wrong type is turned down by the same comparison `app` makes of an argument list, and a hashmap's
-- two-parameter function is exactly what that turns down here.
#guard
  (Expression.listMap (.varRef "xs") (.lam [("x", .string)] (.varRef "x"))).infer types ctx == none

#guard (Expression.listMap (.varRef "xs") (.lam [] (.intLit 1))).infer types ctx == none

#guard
  (Expression.listMap (.varRef "xs") (.lam [("x", .int), ("y", .int)] (.varRef "x"))).infer types
      ctx ==
    none

#guard (Expression.listMap (.varRef "xs") (.varRef "f")).infer types ctx == none

-- Either operand being the wrong kind of thing is enough: the first has to be a list and the second
-- a function.  A hashmap under a list's mapping is turned down here rather than by the tag the
-- surface syntax writes.
#guard (Expression.listMap (.varRef "m") (.lam [("x", .int)] (.varRef "x"))).infer types ctx == none

#guard (Expression.listMap (.varRef "n") (.lam [("x", .int)] (.varRef "x"))).infer types ctx == none

#guard
  (Expression.listMap (.varRef "nope") (.lam [("x", .int)] (.varRef "x"))).infer types ctx == none

#guard (Expression.listMap (.varRef "xs") (.varRef "n")).infer types ctx == none

-- An element type nothing can be compared at is no obstacle, unlike under the hashmap forms: a list
-- compares nothing, so a function type on either side of a mapping is as mappable as any other.
#guard
  (Expression.listMap (.lnil (.fn [.int] .int)) (.lam [("g", .fn [.int] .int)] (.intLit 1))).infer
      types ctx ==
    some (.list .int)

#guard
  (Expression.listMap (.varRef "xs") (.lam [("x", .int)] (.lam [("y", .int)] (.varRef "x")))).infer
      types ctx ==
    some (.list (.fn [.int] .int))

-- What it produces is a list like any other, so the list forms nest into each other — and a
-- conversion's list of tuples is one it reads as well.
#guard
  (Expression.listMap (.listMap (.varRef "xs") (.lam [("x", .int)] (.stringLit "a")))
          (.lam [("s", .string)] (.intLit 0))).infer
      types ctx ==
    some (.list .int)

#guard
  (Expression.listLength (.listMap (.varRef "xs") (.lam [("x", .int)] (.stringLit "a")))).infer
      types ctx ==
    some .int

#guard
  (Expression.listReverse (.listMap (.varRef "xs") (.lam [("x", .int)] (.stringLit "a")))).infer
      types ctx ==
    some (.list .string)

#guard
  (Expression.listMap (.hashmapToList (.varRef "m"))
          (.lam [("p", .tuple [.string, .int])] (.tupleGet (.varRef "p") 1))).infer
      types ctx ==
    some (.list .int)

#guard
  ((Expression.listMap (.varRef "xs") (.lam [("x", .int)] (.varRef "x"))).check types ctx
      (.list .int)).isOk

#guard
  !((Expression.listMap (.varRef "xs") (.lam [("x", .int)] (.varRef "x"))).check types ctx
        (.list .string)).isOk

-- A flat mapping takes its element type from *inside* what the function returns, which is the one
-- place a result type is read a layer in rather than whole: the same function under `map list` gives
-- a list of lists where this gives the list those were run together into.
#guard
  (Expression.listFlatMap (.varRef "xs") (.lam [("x", .int)] (.lnil .string))).infer types ctx ==
    some (.list .string)

#guard
  (Expression.listMap (.varRef "xs") (.lam [("x", .int)] (.lnil .string))).infer types ctx ==
    some (.list (.list .string))

#guard
  (Expression.listFlatMap (.varRef "xs")
          (.lam [("x", .int)] (.lcons (.varRef "x") (.lnil .int)))).infer
      types ctx ==
    some (.list .int)

#guard
  (Expression.listFlatMap (.lnil (.struct "Point"))
          (.lam [("p", .struct "Point")] (.lcons (.structGet (.varRef "p") "x") (.lnil .int)))).infer
      types ctx ==
    some (.list .int)

-- A function returning a list of lists flattens one layer and no further, which is what makes this
-- a form that can be written twice over the same operand.
#guard
  (Expression.listFlatMap (.varRef "xs") (.lam [("x", .int)] (.lnil (.list .string)))).infer types
      ctx ==
    some (.list (.list .string))

-- What the function returns has to be a list: that is the whole of what this asks over `map list`,
-- and it is asked of the function's result type rather than of any element.
#guard
  (Expression.listFlatMap (.varRef "xs") (.lam [("x", .int)] (.varRef "x"))).infer types ctx == none

#guard
  (Expression.listFlatMap (.varRef "xs") (.lam [("x", .int)] (.optionSome (.varRef "x")))).infer
      types ctx ==
    none

#guard
  (Expression.listFlatMap (.varRef "xs") (.lam [("x", .int)] (.hashmapEmpty .string .int))).infer
      types ctx ==
    none

-- The function takes one parameter at the list's element type, as a mapping's does, and either
-- operand being the wrong kind of thing is enough.
#guard
  (Expression.listFlatMap (.varRef "xs") (.lam [("x", .string)] (.lnil .int))).infer types ctx ==
    none

#guard (Expression.listFlatMap (.varRef "xs") (.lam [] (.lnil .int))).infer types ctx == none

#guard
  (Expression.listFlatMap (.varRef "xs") (.lam [("x", .int), ("y", .int)] (.lnil .int))).infer types
      ctx ==
    none

#guard (Expression.listFlatMap (.varRef "xs") (.varRef "f")).infer types ctx == none

#guard
  (Expression.listFlatMap (.varRef "m") (.lam [("x", .int)] (.lnil .int))).infer types ctx == none

#guard
  (Expression.listFlatMap (.varRef "n") (.lam [("x", .int)] (.lnil .int))).infer types ctx == none

#guard
  (Expression.listFlatMap (.varRef "nope") (.lam [("x", .int)] (.lnil .int))).infer types ctx ==
    none

-- What it produces is a list like any other, so the list forms nest into each other.
#guard
  (Expression.listLength (.listFlatMap (.varRef "xs") (.lam [("x", .int)] (.lnil .string)))).infer
      types ctx ==
    some .int

#guard
  (Expression.listFlatMap (.hashmapToList (.varRef "m"))
          (.lam [("q", .tuple [.string, .int])]
            (.lcons (.tupleGet (.varRef "q") 1) (.lnil .int)))).infer
      types ctx ==
    some (.list .int)

#guard
  ((Expression.listFlatMap (.varRef "xs") (.lam [("x", .int)] (.lnil .string))).check types ctx
      (.list .string)).isOk

#guard
  !((Expression.listFlatMap (.varRef "xs") (.lam [("x", .int)] (.lnil .string))).check types ctx
        (.list (.list .string))).isOk

-- A sort passes its operand's type through, the way `reverse` does: the projection's result is the
-- key each element is ordered by, so it goes into the ordering and not into the type.
#guard
  (Expression.listSortOn (.varRef "xs") (.lam [("x", .int)] (.varRef "x"))).infer types ctx ==
    some (.list .int)

#guard
  (Expression.listSortOn (.varRef "xs") (.lam [("x", .int)] (.stringLit "a"))).infer types ctx ==
    some (.list .int)

#guard
  (Expression.listSortOn (.lnil (.struct "Point"))
          (.lam [("p", .struct "Point")] (.structGet (.varRef "p") "x"))).infer
      types ctx ==
    some (.list (.struct "Point"))

-- The projection takes one parameter at the list's element type, which is the comparison a
-- mapping's function is held to as well.
#guard
  (Expression.listSortOn (.varRef "xs") (.lam [("x", .string)] (.varRef "x"))).infer types ctx ==
    none

#guard (Expression.listSortOn (.varRef "xs") (.lam [] (.intLit 1))).infer types ctx == none

#guard
  (Expression.listSortOn (.varRef "xs") (.lam [("x", .int), ("y", .int)] (.intLit 1))).infer types
      ctx ==
    none

#guard (Expression.listSortOn (.varRef "xs") (.varRef "n")).infer types ctx == none

#guard
  (Expression.listSortOn (.varRef "m") (.lam [("x", .int)] (.varRef "x"))).infer types ctx == none

#guard
  (Expression.listSortOn (.varRef "n") (.lam [("x", .int)] (.varRef "x"))).infer types ctx == none

-- The key has to be a type with an ordering, which is what sets this apart from every other list
-- form: `Ty.orderable` accepts `int` and `string` and the three formers that carry them, and turns
-- down a `bool`, a declared type, a hashmap and a function exactly as it does under `lt`.
#guard
  (Expression.listSortOn (.varRef "xs") (.lam [("x", .int)] (.optionSome (.varRef "x")))).infer
      types ctx ==
    some (.list .int)

#guard
  (Expression.listSortOn (.varRef "xs")
          (.lam [("x", .int)] (.tupleNew [.varRef "x", .stringLit "a"]))).infer
      types ctx ==
    some (.list .int)

#guard
  (Expression.listSortOn (.varRef "xs")
          (.lam [("x", .int)] (.lcons (.varRef "x") (.lnil .int)))).infer
      types ctx ==
    some (.list .int)

#guard
  (Expression.listSortOn (.varRef "xs")
          (.lam [("x", .int)] (.equals (.varRef "x") (.intLit 0)))).infer
      types ctx ==
    none

#guard
  (Expression.listSortOn (.lnil (.struct "Point"))
          (.lam [("p", .struct "Point")] (.varRef "p"))).infer
      types ctx ==
    none

#guard
  (Expression.listSortOn (.varRef "xs") (.lam [("x", .int)] (.varRef "c"))).infer types ctx == none

#guard
  (Expression.listSortOn (.varRef "xs") (.lam [("x", .int)] (.varRef "m"))).infer types ctx == none

#guard
  (Expression.listSortOn (.varRef "xs")
          (.lam [("x", .int)] (.lam [("y", .int)] (.varRef "x")))).infer
      types ctx ==
    none

-- An element type with no ordering is no obstacle, which is the other half of the same point: it is
-- the key that is compared, so a list of anything at all can be sorted by an `int` read off it.
#guard
  (Expression.listSortOn (.lnil (.fn [.int] .int))
          (.lam [("g", .fn [.int] .int)] (.intLit 0))).infer
      types ctx ==
    some (.list (.fn [.int] .int))

#guard
  (Expression.listSortOn (.lnil (.hashmap .string .int))
          (.lam [("m'", .hashmap .string .int)] (.intLit 0))).infer
      types ctx ==
    some (.list (.hashmap .string .int))

-- What it produces is a list like any other, so the list forms nest into each other here too.
#guard
  (Expression.listLength (.listSortOn (.varRef "xs") (.lam [("x", .int)] (.varRef "x")))).infer
      types ctx ==
    some .int

#guard
  (Expression.listSortOn (.listMap (.varRef "xs") (.lam [("x", .int)] (.stringLit "a")))
          (.lam [("s", .string)] (.varRef "s"))).infer
      types ctx ==
    some (.list .string)

#guard
  (Expression.listSortOn (.hashmapToList (.varRef "m"))
          (.lam [("p", .tuple [.string, .int])] (.tupleGet (.varRef "p") 1))).infer
      types ctx ==
    some (.list (.tuple [.string, .int]))

#guard
  ((Expression.listSortOn (.varRef "xs") (.lam [("x", .int)] (.varRef "x"))).check types ctx
      (.list .int)).isOk

#guard
  !((Expression.listSortOn (.varRef "xs") (.lam [("x", .int)] (.stringLit "a"))).check types ctx
        (.list .string)).isOk

-- A sort by a comparison passes its operand's type through as well, and the comparison's own type is
-- fixed: two parameters at the element type, and a `bool` back.
#guard
  (Expression.listSortBy (.varRef "xs")
          (.lam [("a", .int), ("b", .int)] (.le (.varRef "a") (.varRef "b")))).infer
      types ctx ==
    some (.list .int)

#guard
  (Expression.listSortBy (.lnil (.struct "Point"))
          (.lam [("p", .struct "Point"), ("q", .struct "Point")]
            (.lt (.structGet (.varRef "p") "x") (.structGet (.varRef "q") "x")))).infer
      types ctx ==
    some (.list (.struct "Point"))

-- Two parameters, both at the element type: one is the arity a projection has, and either parameter
-- at another type is the comparison of another list.
#guard
  (Expression.listSortBy (.varRef "xs") (.lam [("x", .int)] (.boolLit true))).infer types ctx ==
    none

#guard
  (Expression.listSortBy (.varRef "xs")
          (.lam [("a", .int), ("b", .int), ("c", .int)] (.boolLit true))).infer
      types ctx ==
    none

#guard
  (Expression.listSortBy (.varRef "xs")
          (.lam [("a", .int), ("b", .string)] (.boolLit true))).infer
      types ctx ==
    none

#guard
  (Expression.listSortBy (.varRef "xs")
          (.lam [("a", .string), ("b", .string)] (.boolLit true))).infer
      types ctx ==
    none

#guard (Expression.listSortBy (.varRef "xs") (.varRef "n")).infer types ctx == none

#guard
  (Expression.listSortBy (.varRef "m")
          (.lam [("a", .int), ("b", .int)] (.boolLit true))).infer
      types ctx ==
    none

#guard
  (Expression.listSortBy (.varRef "n")
          (.lam [("a", .int), ("b", .int)] (.boolLit true))).infer
      types ctx ==
    none

-- The result has to be a `bool`, which is where the two sorts part company: a comparison answering
-- with an `int` is turned down where a projection returning one is exactly what `sortOn` wants.
#guard
  (Expression.listSortBy (.varRef "xs")
          (.lam [("a", .int), ("b", .int)] (.plus (.varRef "a") (.varRef "b")))).infer
      types ctx ==
    none

#guard
  (Expression.listSortBy (.varRef "xs")
          (.lam [("a", .int), ("b", .int)] (.optionSome (.boolLit true)))).infer
      types ctx ==
    none

-- And nothing is asked of the element type, which is the other half of the same point: the elements
-- go into the comparison and nowhere else, so a list of the types no ordering reaches can be sorted
-- where `sortOn` could only order it by a key read off it.
#guard
  (Expression.listSortBy (.lnil (.fn [.int] .int))
          (.lam [("g", .fn [.int] .int), ("h", .fn [.int] .int)] (.boolLit true))).infer
      types ctx ==
    some (.list (.fn [.int] .int))

#guard
  (Expression.listSortBy (.lnil (.hashmap .string .int))
          (.lam [("m1", .hashmap .string .int), ("m2", .hashmap .string .int)]
            (.boolLit true))).infer
      types ctx ==
    some (.list (.hashmap .string .int))

#guard
  (Expression.listSortBy (.lnil .bool)
          (.lam [("a", .bool), ("b", .bool)] (.varRef "a"))).infer
      types ctx ==
    some (.list .bool)

-- What it produces is a list like any other, so the list forms nest into each other here too — the
-- two sorts among them.
#guard
  (Expression.listSortBy (.listSortOn (.varRef "xs") (.lam [("x", .int)] (.varRef "x")))
          (.lam [("a", .int), ("b", .int)] (.le (.varRef "a") (.varRef "b")))).infer
      types ctx ==
    some (.list .int)

#guard
  (Expression.listSortBy (.hashmapToList (.varRef "m"))
          (.lam [("p", .tuple [.string, .int]), ("q", .tuple [.string, .int])]
            (.le (.tupleGet (.varRef "p") 1) (.tupleGet (.varRef "q") 1)))).infer
      types ctx ==
    some (.list (.tuple [.string, .int]))

#guard
  ((Expression.listSortBy (.varRef "xs")
        (.lam [("a", .int), ("b", .int)] (.le (.varRef "a") (.varRef "b")))).check types ctx
      (.list .int)).isOk

#guard
  !((Expression.listSortBy (.varRef "xs")
          (.lam [("a", .int), ("b", .int)] (.le (.varRef "a") (.varRef "b")))).check types ctx
        (.list .bool)).isOk

-- A search holds its predicate to one parameter at the element type and a `bool` back, and what
-- comes out mentions neither: an `option int` whatever the list held, which is the one list type
-- that is neither a list nor an `int`.
#guard
  (Expression.listFindIndex (.varRef "xs")
          (.lam [("x", .int)] (.equals (.varRef "x") (.intLit 0)))).infer
      types ctx ==
    some (.option .int)

#guard
  (Expression.listFindIndex (.lnil (.struct "Point"))
          (.lam [("p", .struct "Point")] (.lt (.structGet (.varRef "p") "x") (.intLit 0)))).infer
      types ctx ==
    some (.option .int)

-- One parameter, where a comparison takes two: the arity is what tells a predicate from a
-- comparison, both of them answering with a `bool`.
#guard
  (Expression.listFindIndex (.varRef "xs")
          (.lam [("a", .int), ("b", .int)] (.boolLit true))).infer
      types ctx ==
    none

#guard (Expression.listFindIndex (.varRef "xs") (.lam [] (.boolLit true))).infer types ctx == none

#guard
  (Expression.listFindIndex (.varRef "xs") (.lam [("x", .string)] (.boolLit true))).infer types
      ctx ==
    none

#guard (Expression.listFindIndex (.varRef "xs") (.varRef "n")).infer types ctx == none

#guard
  (Expression.listFindIndex (.varRef "m") (.lam [("x", .int)] (.boolLit true))).infer types ctx ==
    none

#guard
  (Expression.listFindIndex (.varRef "n") (.lam [("x", .int)] (.boolLit true))).infer types ctx ==
    none

#guard
  (Expression.listFindIndex (.varRef "nope") (.lam [("x", .int)] (.boolLit true))).infer types
      ctx ==
    none

-- The result has to be a `bool`, as a comparison's does: a predicate answering with the element it
-- was handed is turned down where `sortOn` would take it as a key.
#guard
  (Expression.listFindIndex (.varRef "xs") (.lam [("x", .int)] (.varRef "x"))).infer types ctx ==
    none

#guard
  (Expression.listFindIndex (.varRef "xs")
          (.lam [("x", .int)] (.optionSome (.boolLit true)))).infer
      types ctx ==
    none

-- And nothing is asked of the element type, for the reason `sortBy` asks nothing of it: the
-- elements go into the predicate and nowhere else, so a list of the types no ordering reaches can
-- be searched.
#guard
  (Expression.listFindIndex (.lnil (.fn [.int] .int))
          (.lam [("g", .fn [.int] .int)] (.boolLit true))).infer
      types ctx ==
    some (.option .int)

#guard
  (Expression.listFindIndex (.lnil (.hashmap .string .int))
          (.lam [("m'", .hashmap .string .int)] (.boolLit true))).infer
      types ctx ==
    some (.option .int)

-- It reads a list like any other and what it produces is an option like any other, so a match takes
-- it apart where every other list form hands the next one a list.
#guard
  (Expression.listFindIndex (.listSortOn (.varRef "xs") (.lam [("x", .int)] (.varRef "x")))
          (.lam [("x", .int)] (.equals (.varRef "x") (.intLit 0)))).infer
      types ctx ==
    some (.option .int)

#guard
  (Expression.listFindIndex (.hashmapToList (.varRef "m"))
          (.lam [("p", .tuple [.string, .int])]
            (.equals (.tupleGet (.varRef "p") 1) (.intLit 0)))).infer
      types ctx ==
    some (.option .int)

#guard
  (Expression.optionMatch
          (.listFindIndex (.varRef "xs") (.lam [("x", .int)] (.equals (.varRef "x") (.intLit 0))))
          (.intLit 0) "i" (.varRef "i")).infer
      types ctx ==
    some .int

#guard
  ((Expression.listFindIndex (.varRef "xs")
        (.lam [("x", .int)] (.equals (.varRef "x") (.intLit 0)))).check types ctx
      (.option .int)).isOk

#guard
  !((Expression.listFindIndex (.varRef "xs")
          (.lam [("x", .int)] (.equals (.varRef "x") (.intLit 0)))).check types ctx .int).isOk

-- A `lam` takes its parameter types from its annotation and its result type from its body.
#guard (Expression.lam [("x", .int)] (.varRef "x")).infer types ctx == some (.fn [.int] .int)

#guard
  (Expression.lam [("x", .int), ("y", .string)] (.varRef "y")).infer types ctx ==
    some (.fn [.int, .string] .string)

#guard (Expression.lam [] (.intLit 1)).infer types ctx == some (.fn [] .int)

#guard (Expression.lam [("x", .int)] (.varRef "nope")).infer types ctx == none

#guard (Expression.lam [("x", .string)] (.plus (.varRef "x") (.intLit 1))).infer types ctx == none

-- A body sees the enclosing context as well as the parameters, and the parameters shadow it.
#guard
  (Expression.lam [("x", .int)] (.plus (.varRef "x") (.varRef "n"))).infer types ctx ==
    some (.fn [.int] .int)

#guard
  (Expression.lam [("n", .string)] (.varRef "n")).infer types ctx == some (.fn [.string] .string)

#guard
  (Expression.lam [("x", .int), ("x", .string)] (.varRef "x")).infer types ctx ==
    some (.fn [.int, .string] .int)

-- Function types are types like any other: a `lam` can return one, and a list can hold them.
#guard
  (Expression.lam [("x", .int)] (.lam [("y", .string)] (.varRef "x"))).infer types ctx ==
    some (.fn [.int] (.fn [.string] .int))

#guard
  (Expression.lcons (.varRef "f") (.lnil (.fn [.int, .string] .int))).infer types ctx ==
    some (.list (.fn [.int, .string] .int))

#guard (Expression.lcons (.varRef "f") (.lnil (.fn [.int] .int))).infer types ctx == none

-- An `app` needs a function, and arguments whose types are the parameter types in order.
#guard (Expression.app (.varRef "f") [.intLit 1, .stringLit "a"]).infer types ctx == some .int

#guard
  (Expression.app (.lam [("x", .int)] (.plus (.varRef "x") (.intLit 1))) [.intLit 2]).infer types
      ctx ==
    some .int

#guard (Expression.app (.lam [] (.intLit 1)) []).infer types ctx == some .int

#guard (Expression.app (.varRef "f") [.stringLit "a", .intLit 1]).infer types ctx == none

#guard (Expression.app (.varRef "f") [.varRef "nope", .stringLit "a"]).infer types ctx == none

#guard (Expression.app (.varRef "n") [.intLit 1]).infer types ctx == none

#guard (Expression.app (.lnil .int) []).infer types ctx == none

-- Arity is part of the function type, so a call with the wrong number of arguments is ill typed
-- rather than partially applied.
#guard (Expression.app (.varRef "f") [.intLit 1]).infer types ctx == none

#guard (Expression.app (.varRef "f") []).infer types ctx == none

#guard (Expression.app (.varRef "f") [.intLit 1, .stringLit "a", .intLit 2]).infer types ctx == none

-- Applying a function that returns a function gives the inner function type, which can then be
-- applied in turn.
#guard
  (Expression.app (.lam [("x", .int)] (.lam [("y", .string)] (.varRef "x"))) [.intLit 1]).infer
      types ctx ==
    some (.fn [.string] .int)

#guard
  (Expression.app (.app (.lam [("x", .int)] (.lam [("y", .string)] (.varRef "x"))) [.intLit 1])
          [.stringLit "a"]).infer
      types ctx ==
    some .int

-- A `let_` gives its body's type, with the bound name at the type inferred for what it binds.
#guard
  (Expression.let_ "x" (.intLit 1) (.plus (.varRef "x") (.intLit 2))).infer types ctx == some .int

#guard (Expression.let_ "x" (.stringLit "a") (.varRef "x")).infer types ctx == some .string

#guard (Expression.let_ "x" (.varRef "xs") (.varRef "x")).infer types ctx == some (.list .int)

#guard
  (Expression.let_ "g" (.lam [("y", .int)] (.varRef "y")) (.app (.varRef "g") [.intLit 1])).infer
      types ctx ==
    some .int

-- An ill-typed expression on either side makes the whole `let_` ill typed.
#guard (Expression.let_ "x" (.varRef "nope") (.intLit 1)).infer types ctx == none

#guard
  (Expression.let_ "x" (.intLit 1) (.plus (.varRef "x") (.stringLit "a"))).infer types ctx == none

#guard (Expression.let_ "x" (.intLit 1) (.varRef "nope")).infer types ctx == none

-- The name is added after the expression it binds is typed, so a `let_` is not recursive: the bound
-- expression sees the enclosing context only.
#guard (Expression.let_ "x" (.varRef "x") (.varRef "x")).infer types ctx == none

#guard
  (Expression.let_ "n" (.plus (.varRef "n") (.intLit 1)) (.varRef "n")).infer types ctx == some .int

-- The binding shadows an enclosing one of the same name, inner `let_`s included.
#guard (Expression.let_ "n" (.stringLit "a") (.varRef "n")).infer types ctx == some .string

#guard
  (Expression.let_ "n" (.stringLit "a") (.plus (.varRef "n") (.intLit 1))).infer types ctx == none

#guard
  (Expression.let_ "x" (.intLit 1) (.let_ "x" (.stringLit "a") (.varRef "x"))).infer types ctx ==
    some .string

-- `let_`s nest, and a later one sees what an earlier one bound.
#guard
  (Expression.let_ "x" (.intLit 1)
          (.let_ "y" (.plus (.varRef "x") (.intLit 1)) (.plus (.varRef "x") (.varRef "y")))).infer
      types ctx ==
    some .int

-- A `lam` body sees a `let_` from outside it, and a `let_` body sees the parameters.
#guard
  (Expression.let_ "x" (.intLit 1) (.lam [("y", .int)] (.plus (.varRef "x") (.varRef "y")))).infer
      types ctx ==
    some (.fn [.int] .int)

#guard
  (Expression.lam [("y", .int)] (.let_ "x" (.varRef "y") (.plus (.varRef "x") (.varRef "y")))).infer
      types ctx ==
    some (.fn [.int] .int)

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

#guard ((Expression.boolLit true).check types ctx .bool).isOk

#guard !((Expression.boolLit true).check types ctx .int).isOk

#guard !((Expression.boolLit false).check types ctx (.list .bool)).isOk

-- So a literal goes wherever a `bool` goes: into a list of them, into a conditional's branches, and
-- into a call expecting one.
#guard (Expression.lcons (.boolLit true) (.lnil .bool)).infer types ctx == some (.list .bool)

#guard
  (Expression.lcons (.boolLit true) (.lcons (.varRef "flag") (.lnil .bool))).infer types ctx ==
    some (.list .bool)

#guard (Expression.lcons (.boolLit true) (.lnil .int)).infer types ctx == none

#guard
  (Expression.app (.lam [("q", .bool)] (.varRef "q")) [.boolLit true]).infer types ctx == some .bool

#guard (Expression.app (.lam [("q", .int)] (.varRef "q")) [.boolLit true]).infer types ctx == none

#guard (Expression.plus (.boolLit true) (.intLit 1)).infer types ctx == none

-- A conditional takes its type from its branches, whatever type that is.
#guard (Expression.ite (.varRef "flag") (.intLit 1) (.intLit 2)).infer types ctx == some .int

#guard
  (Expression.ite (.varRef "flag") (.stringLit "a") (.varRef "s")).infer types ctx == some .string

#guard
  (Expression.ite (.varRef "flag") (.varRef "xs") (.lnil .int)).infer types ctx == some (.list .int)

#guard
  (Expression.ite (.varRef "flag") (.varRef "p") (.varRef "p")).infer types ctx ==
    some (.struct "Point")

#guard
  (Expression.ite (.varRef "flag") (.varRef "c") (.indNew "Color" "Red" [])).infer types ctx ==
    some (.ind "Color")

#guard
  (Expression.ite (.varRef "flag") (.varRef "f") (.varRef "f")).infer types ctx ==
    some (.fn [.int, .string] .int)

#guard
  (Expression.ite (.varRef "flag") (.varRef "flag") (.varRef "flag")).infer types ctx == some .bool

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

#guard
  (Expression.ite (.boolLit true) (.boolLit false) (.varRef "flag")).infer types ctx == some .bool

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
#guard
  (Expression.plus (.ite (.varRef "flag") (.intLit 1) (.intLit 2)) (.intLit 1)).infer types ctx ==
    some .int

#guard
  (Expression.ite (.ite (.varRef "flag") (.varRef "flag") (.varRef "flag")) (.intLit 1)
          (.intLit 2)).infer
      types ctx ==
    some .int

#guard
  (Expression.ite (.varRef "flag") (.ite (.varRef "flag") (.intLit 1) (.intLit 2))
          (.intLit 3)).infer
      types ctx ==
    some .int

#guard
  (Expression.lam [("q", .bool)] (.ite (.varRef "q") (.intLit 1) (.intLit 2))).infer types ctx ==
    some (.fn [.bool] .int)

#guard
  (Expression.let_ "q" (.varRef "flag") (.ite (.varRef "q") (.intLit 1) (.intLit 2))).infer types
      ctx ==
    some .int

#guard
  (Expression.indMatch (.varRef "c")
          [("Red", [], .ite (.varRef "flag") (.intLit 0) (.intLit 1)), ("Green", [], .intLit 1),
            ("Blue", [], .intLit 2)]).infer
      types ctx ==
    some .int

-- The two boolean operators are `plus` and `minus` over `bool`: one type on both sides and the same
-- type out.  Which of the two it is makes no difference to typing — that is a question about
-- evaluating them — so every case below holds of both.
#guard (Expression.boolAnd (.varRef "flag") (.varRef "flag")).infer types ctx == some .bool

#guard (Expression.boolOr (.varRef "flag") (.varRef "flag")).infer types ctx == some .bool

#guard (Expression.boolAnd (.boolLit true) (.boolLit false)).infer types ctx == some .bool

#guard (Expression.boolOr (.boolLit true) (.boolLit false)).infer types ctx == some .bool

#guard (Expression.boolAnd (.boolLit true) (.boolLit false)).infer {} [] == some .bool

#guard ((Expression.boolAnd (.varRef "flag") (.boolLit true)).check types ctx .bool).isOk

#guard !((Expression.boolAnd (.varRef "flag") (.boolLit true)).check types ctx .int).isOk

-- Both operands have to be `bool`s, on either side and whatever else they are: there is no
-- truthiness, so nothing else will do, exactly as for a conditional's condition.
#guard (Expression.boolAnd (.intLit 1) (.boolLit true)).infer types ctx == none

#guard (Expression.boolAnd (.boolLit true) (.intLit 1)).infer types ctx == none

#guard (Expression.boolOr (.varRef "n") (.varRef "flag")).infer types ctx == none

#guard (Expression.boolOr (.varRef "flag") (.varRef "s")).infer types ctx == none

#guard (Expression.boolAnd (.varRef "xs") (.varRef "flag")).infer types ctx == none

#guard (Expression.boolAnd (.varRef "flag") (.varRef "c")).infer types ctx == none

#guard (Expression.boolOr (.varRef "flag") (.lnil .bool)).infer types ctx == none

-- An ill-typed operand makes the whole thing ill typed, the operand that would not have been
-- evaluated included: typing says nothing about which of them settles the answer.
#guard (Expression.boolAnd (.varRef "nope") (.varRef "flag")).infer types ctx == none

#guard (Expression.boolAnd (.boolLit false) (.varRef "nope")).infer types ctx == none

#guard (Expression.boolOr (.boolLit true) (.varRef "nope")).infer types ctx == none

-- What they produce is a `bool`, so they nest in each other and in every other form that takes one
-- — and a comparison is what most of their operands are, since that is where a `bool` comes from.
#guard
  (Expression.boolAnd (.boolAnd (.varRef "flag") (.varRef "flag"))
          (.boolOr (.varRef "flag") (.boolLit true))).infer
      types ctx ==
    some .bool

#guard
  (Expression.boolAnd (.equals (.varRef "n") (.intLit 1))
          (.equals (.varRef "s") (.stringLit "a"))).infer
      types ctx ==
    some .bool

#guard
  (Expression.boolOr (.equals (.varRef "xs") (.lnil .int))
          (.equals (.varRef "p") (.varRef "p"))).infer
      types ctx ==
    some .bool

#guard
  (Expression.ite (.boolOr (.varRef "flag") (.boolLit false)) (.intLit 1) (.intLit 2)).infer types
      ctx ==
    some .int

#guard
  (Expression.lam [("q", .bool)] (.boolAnd (.varRef "q") (.varRef "flag"))).infer types ctx ==
    some (.fn [.bool] .bool)

#guard
  (Expression.lcons (.boolAnd (.varRef "flag") (.boolLit true)) (.lnil .bool)).infer types ctx ==
    some (.list .bool)

#guard
  (Expression.equals (.boolAnd (.varRef "flag") (.boolLit true)) (.boolLit false)).infer types
      ctx ==
    some .bool

#guard
  (Expression.plus (.boolAnd (.varRef "flag") (.boolLit true)) (.intLit 1)).infer types ctx == none

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
  {
    ss :=
      Structs.ofDecls
        [{ name := "C1", fields := [("n", .struct "C2")] },
          { name := "C2", fields := [("n", .struct "C3")] },
          { name := "C3", fields := [("n", .struct "C4")] },
          { name := "C4", fields := [("step", .fn [.int] .int)] }] }

#guard !Ty.comparable chain (.struct "C1")

#guard !Ty.comparable chain (.struct "C4")

/-- The same chain ending in a name the table does not declare, which takes one step more than the
one ending in a function type: the name has to be *reached* for its lookup to fail. -/
private def chainMissing : TypeDecls :=
  {
    ss :=
      Structs.ofDecls
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
  {
    ss :=
      Structs.ofDecls
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

#guard
  (Expression.equals (.lam [("x", .int)] (.varRef "x")) (.lam [("x", .int)] (.varRef "x"))).infer
      types ctx ==
    none

#guard
  (Expression.equals (.lnil (.fn [.int] .int)) (.lnil (.fn [.int] .int))).infer types ctx == none

#guard (Expression.equals (.varRef "wf") (.varRef "wf")).infer types ctx == none

#guard (Expression.equals (.varRef "hd") (.varRef "hd")).infer types ctx == none

-- A struct type whose declaration the table does not have is no more comparable than the comparison
-- is typeable without it.
#guard (Expression.equals (.varRef "p") (.varRef "p")).infer {} ctx == none

-- A comparison is an expression like any other: it goes where a `bool` goes, and its operands are
-- whatever has the type they share.
#guard
  (Expression.ite (.equals (.varRef "n") (.intLit 1)) (.intLit 1) (.intLit 2)).infer types ctx ==
    some .int

#guard
  (Expression.equals (.equals (.varRef "n") (.intLit 1)) (.varRef "flag")).infer types ctx ==
    some .bool

#guard
  (Expression.equals (.plus (.varRef "n") (.intLit 1)) (.varRef "n")).infer types ctx == some .bool

#guard (Expression.equals (.structGet (.varRef "p") "x") (.intLit 0)).infer types ctx == some .bool

#guard
  (Expression.equals (.lcons (.intLit 1) (.varRef "xs")) (.varRef "xs")).infer types ctx ==
    some .bool

#guard
  (Expression.lam [("q", .ind "Tree")] (.equals (.varRef "q") (.varRef "t"))).infer types ctx ==
    some (.fn [.ind "Tree"] .bool)

#guard
  (Expression.let_ "e" (.equals (.varRef "n") (.intLit 1)) (.varRef "e")).infer types ctx ==
    some .bool

/-! ### Ordering

Which types an ordering may be used at, which is `Ty.orderable`, and then what `lt` and `le` do with
it: one type between the two operands, and a `bool` out of it whatever that type was.  The two forms
have one rule between them, so each guard below holds of either wherever it holds of one. -/

-- `int` and `string` are the leaves with an ordering.  A `bool` is not one of them, which is where
-- this parts company with `Ty.comparable`: it is what a comparison produces, not what one compares.
#guard Ty.orderable .int

#guard Ty.orderable .string

#guard !Ty.orderable .bool

#guard !Ty.orderable (.fn [.int] .int)

#guard !Ty.orderable (.hashmap .string .int)

-- An option, a list and a tuple are ordered exactly when the types they hold are, however deeply
-- nested.
#guard Ty.orderable (.option .int)

#guard Ty.orderable (.option (.list .string))

#guard Ty.orderable (.list .int)

#guard Ty.orderable (.list (.list .string))

#guard Ty.orderable (.tuple [.string, .int])

#guard Ty.orderable (.tuple [])

#guard !Ty.orderable (.option .bool)

#guard !Ty.orderable (.list .bool)

#guard !Ty.orderable (.list (.fn [.int] .int))

#guard !Ty.orderable (.tuple [.string, .bool])

#guard !Ty.orderable (.tuple [.int, .hashmap .string .int])

-- A declared type is turned down whatever it declares, so there is nothing to look up and no budget
-- to run out: `Point` is two `int`s and is no more ordered than `WithFn` is.
#guard !Ty.orderable (.struct "Point")

#guard !Ty.orderable (.struct "WithFn")

#guard !Ty.orderable (.ind "Color")

#guard !Ty.orderable (.ind "Tree")

#guard !Ty.orderable (.list (.struct "Point"))

-- Two operands of one ordered type make a `bool`, whatever that type was.
#guard (Expression.lt (.intLit 1) (.intLit 2)).infer types ctx == some .bool

#guard (Expression.le (.intLit 1) (.intLit 2)).infer types ctx == some .bool

#guard (Expression.lt (.stringLit "a") (.varRef "s")).infer types ctx == some .bool

#guard (Expression.le (.varRef "xs") (.lnil .int)).infer types ctx == some .bool

#guard (Expression.lt (.varRef "o") (.optionNone .int)).infer types ctx == some .bool

#guard (Expression.le (.varRef "tu") (.varRef "tu")).infer types ctx == some .bool

#guard (Expression.lt (.intLit 1) (.intLit 2)).infer {} [] == some .bool

-- The type is read off the left operand and then required of the right, so operands of different
-- types have nothing to compare.
#guard (Expression.lt (.intLit 1) (.stringLit "a")).infer types ctx == none

#guard (Expression.le (.varRef "xs") (.varRef "n")).infer types ctx == none

#guard (Expression.lt (.lnil .int) (.lnil .string)).infer types ctx == none

-- An ill-typed operand on either side makes the comparison ill typed.
#guard (Expression.lt (.varRef "nope") (.intLit 1)).infer types ctx == none

#guard (Expression.le (.intLit 1) (.varRef "nope")).infer types ctx == none

-- Operands of a type with no ordering are turned down, and the types equality accepts are among
-- them: a `bool`, a struct, an inductive type, a hashmap.
#guard (Expression.lt (.varRef "flag") (.boolLit true)).infer types ctx == none

#guard (Expression.le (.varRef "p") (.varRef "p")).infer types ctx == none

#guard (Expression.lt (.varRef "c") (.varRef "c")).infer types ctx == none

#guard (Expression.le (.varRef "m") (.varRef "m")).infer types ctx == none

#guard (Expression.lt (.varRef "f") (.varRef "f")).infer types ctx == none

#guard (Expression.lt (.varRef "tufn") (.varRef "tufn")).infer types ctx == none

-- The same operands compared for equality are accepted, which is the whole of what the two
-- comparisons differ in.
#guard (Expression.equals (.varRef "flag") (.boolLit true)).infer types ctx == some .bool

#guard (Expression.equals (.varRef "p") (.varRef "p")).infer types ctx == some .bool

-- An ordering is an expression like any other: it goes where a `bool` goes, and its operands are
-- whatever has the type they share.
#guard
  (Expression.ite (.lt (.varRef "n") (.intLit 1)) (.intLit 1) (.intLit 2)).infer types ctx ==
    some .int

#guard
  (Expression.boolAnd (.le (.intLit 0) (.varRef "n")) (.lt (.varRef "n") (.intLit 10))).infer types
      ctx ==
    some .bool

#guard
  (Expression.equals (.lt (.varRef "n") (.intLit 1)) (.varRef "flag")).infer types ctx == some .bool

#guard (Expression.lt (.plus (.varRef "n") (.intLit 1)) (.varRef "n")).infer types ctx == some .bool

#guard (Expression.le (.listLength (.varRef "xs")) (.intLit 0)).infer types ctx == some .bool

#guard (Expression.lt (.structGet (.varRef "p") "x") (.intLit 0)).infer types ctx == some .bool

#guard
  (Expression.lam [("q", .string)] (.lt (.varRef "q") (.varRef "s"))).infer types ctx ==
    some (.fn [.string] .bool)

-- Checking agrees with inference on both forms.
#guard ((Expression.lt (.varRef "n") (.intLit 1)).check types ctx .bool).isOk

#guard !((Expression.lt (.varRef "n") (.intLit 1)).check types ctx .int).isOk

#guard ((Expression.le (.varRef "s") (.stringLit "a")).check types ctx .bool).isOk

#guard !((Expression.le (.varRef "flag") (.boolLit true)).check types ctx .bool).isOk

-- Checking agrees with inference.
#guard ((Expression.lnil .int).check types ctx (.list .int)).isOk

#guard !((Expression.lnil .int).check types ctx .int).isOk

#guard ((Expression.plus (.varRef "n") (.intLit 1)).check types ctx .int).isOk

#guard !((Expression.plus (.varRef "n") (.intLit 1)).check types ctx (.list .int)).isOk

#guard !((Expression.plus (.varRef "n") (.lnil .int)).check types ctx .int).isOk

#guard ((Expression.stringLit "hi").check types ctx .string).isOk

#guard !((Expression.stringLit "hi").check types ctx .int).isOk

#guard ((Expression.lam [("x", .int)] (.varRef "x")).check types ctx (.fn [.int] .int)).isOk

#guard !((Expression.lam [("x", .int)] (.varRef "x")).check types ctx (.fn [.string] .string)).isOk

#guard !((Expression.lam [("x", .int)] (.varRef "x")).check types ctx .int).isOk

/-- `fun (x : int) (y : int) => x + (y - 1)` -/
private def addPred : FuncDecl where
  docstring := "Add `x` to one less than `y`."
  name := "add-pred"
  parameters := [("x", .int), ("y", .int)]
  body := .plus (.varRef "x") (.minus (.varRef "y") (.intLit 1))
  resultType := .int

-- A declaration checks when its body agrees with the result type it declares.
#guard (addPred.check {} []).isOk

#guard !(({ addPred with resultType := .list .int } : FuncDecl).check {} []).isOk

-- The parameter list is all the body has to work with, and it is checked at the types it gives.
#guard !(({ addPred with parameters := [("x", .int)] } : FuncDecl).check {} []).isOk

#guard
  !(({ addPred with parameters := [("x", .int), ("y", .list .int)] } : FuncDecl).check {} []).isOk

/-- `fun (s : string) => ["!", s]` -/
private def bang : FuncDecl where
  docstring := "Put `s` after an exclamation mark."
  name := "bang"
  parameters := [("s", .string)]
  body := .lcons (.stringLit "!") (.lcons (.varRef "s") (.lnil .string))
  resultType := .list .string

#guard (bang.check {} []).isOk

#guard !(({ bang with resultType := .list .int } : FuncDecl).check {} []).isOk

#guard !(({ bang with parameters := [("s", .int)] } : FuncDecl).check {} []).isOk

/-- `fun (g : (int) -> int) (x : int) => g(x)` -/
private def applyTo : FuncDecl where
  docstring := "Call `g` on `x`."
  name := "apply-to"
  parameters := [("g", .fn [.int] .int), ("x", .int)]
  body := .app (.varRef "g") [.varRef "x"]
  resultType := .int

-- A parameter of function type is callable, at the arity and types its type gives.
#guard (applyTo.check {} []).isOk

#guard
  !(({ applyTo with parameters := [("g", .fn [.string] .int), ("x", .int)] } : FuncDecl).check {}
        []).isOk

#guard
  !(({ applyTo with parameters := [("g", .fn [.int, .int] .int), ("x", .int)] } : FuncDecl).check {}
        []).isOk

#guard !(({ applyTo with resultType := .string } : FuncDecl).check {} []).isOk

/-- `fun (n : int) => fun (m : int) => n + m` -/
private def adder : FuncDecl where
  docstring := "Build a function that adds `n` to its argument."
  name := "adder"
  parameters := [("n", .int)]
  body := .lam [("m", .int)] (.plus (.varRef "n") (.varRef "m"))
  resultType := .fn [.int] .int

-- A declaration can return a function, and its result type is checked like any other.
#guard (adder.check {} []).isOk

#guard !(({ adder with resultType := .int } : FuncDecl).check {} []).isOk

#guard !(({ adder with resultType := .fn [.string] .int } : FuncDecl).check {} []).isOk

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

#guard
  (Expression.lcons (.varRef "p") (.lnil (.struct "Point"))).infer types ctx ==
    some (.list (.struct "Point"))

#guard (Expression.lcons (.varRef "p") (.lnil (.struct "Pair"))).infer types ctx == none

-- A `structNew` initializing every declared field at the declared type has the struct's type.
#guard
  (Expression.structNew "Point" [("x", .intLit 1), ("y", .intLit 2)]).infer types ctx ==
    some (.struct "Point")

#guard
  (Expression.structNew "Point" [("x", .varRef "n"), ("y", .plus (.varRef "n") (.intLit 1))]).infer
      types ctx ==
    some (.struct "Point")

#guard
  (Expression.structNew "Box"
          [("label", .stringLit "b"), ("items", .varRef "xs"), ("origin", .varRef "p")]).infer
      types ctx ==
    some (.struct "Box")

-- In any order: the fields are matched up by name, so where they are written is not part of it.
#guard
  (Expression.structNew "Point" [("y", .intLit 2), ("x", .intLit 1)]).infer types ctx ==
    some (.struct "Point")

#guard
  (Expression.structNew "Box"
          [("origin", .varRef "p"), ("label", .stringLit "b"), ("items", .varRef "xs")]).infer
      types ctx ==
    some (.struct "Box")

-- The type each field is held to is the one declared under its own name rather than the one at its
-- position, which is what a reordering has to keep right to be accepted at all.
#guard
  (Expression.structNew "Box"
          [("items", .stringLit "b"), ("label", .varRef "xs"), ("origin", .varRef "p")]).infer
      types ctx ==
    none

-- Every field still has to be there, once, and at the right type.
#guard (Expression.structNew "Point" [("x", .intLit 1)]).infer types ctx == none

#guard (Expression.structNew "Point" []).infer types ctx == none

#guard
  (Expression.structNew "Point" [("x", .intLit 1), ("y", .intLit 2), ("z", .intLit 3)]).infer types
      ctx ==
    none

#guard
  (Expression.structNew "Point" [("z", .intLit 3), ("x", .intLit 1), ("y", .intLit 2)]).infer types
      ctx ==
    none

#guard (Expression.structNew "Point" [("x", .intLit 1), ("x", .intLit 2)]).infer types ctx == none

#guard
  (Expression.structNew "Point" [("x", .intLit 1), ("y", .stringLit "a")]).infer types ctx == none

#guard
  (Expression.structNew "Point" [("y", .stringLit "a"), ("x", .intLit 1)]).infer types ctx == none

#guard
  (Expression.structNew "Point" [("x", .intLit 1), ("y", .varRef "nope")]).infer types ctx == none

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

#guard
  (Expression.listReverse (.structGet (.varRef "b") "items")).infer types ctx == some (.list .int)

#guard
  (Expression.structGet (.structNew "Point" [("x", .intLit 1), ("y", .intLit 2)]) "x").infer types
      ctx ==
    some .int

-- A field the declaration does not list is not a field, and only a struct has fields at all.
#guard (Expression.structGet (.varRef "p") "z").infer types ctx == none

#guard (Expression.structGet (.varRef "b") "x").infer types ctx == none

#guard (Expression.structGet (.varRef "n") "x").infer types ctx == none

#guard (Expression.structGet (.varRef "xs") "x").infer types ctx == none

#guard (Expression.structGet (.varRef "f") "x").infer types ctx == none

#guard (Expression.structGet (.varRef "nope") "x").infer types ctx == none

#guard (Expression.structGet (.varRef "p") "x").infer {} ctx == none

-- `structUpdate` keeps the type it was given, and may name its fields in any order.
#guard
  (Expression.structUpdate (.varRef "p") [("x", .intLit 1)]).infer types ctx ==
    some (.struct "Point")

#guard
  (Expression.structUpdate (.varRef "p") [("y", .intLit 2), ("x", .intLit 1)]).infer types ctx ==
    some (.struct "Point")

#guard
  (Expression.structUpdate (.varRef "b") [("origin", .varRef "p")]).infer types ctx ==
    some (.struct "Box")

-- Which is what lets updates chain, and lets one be read straight away.
#guard
  (Expression.structUpdate (.structUpdate (.varRef "p") [("x", .intLit 1)])
          [("y", .intLit 2)]).infer
      types ctx ==
    some (.struct "Point")

#guard
  (Expression.structGet (.structUpdate (.varRef "p") [("x", .intLit 1)]) "x").infer types ctx ==
    some .int

-- Only a declared field, only at its declared type, and never none of them.
#guard (Expression.structUpdate (.varRef "p") []).infer types ctx == none

#guard (Expression.structUpdate (.varRef "p") [("z", .intLit 1)]).infer types ctx == none

#guard (Expression.structUpdate (.varRef "p") [("x", .stringLit "a")]).infer types ctx == none

#guard
  (Expression.structUpdate (.varRef "p") [("x", .intLit 1), ("z", .intLit 2)]).infer types ctx ==
    none

#guard (Expression.structUpdate (.varRef "p") [("x", .varRef "nope")]).infer types ctx == none

#guard (Expression.structUpdate (.varRef "n") [("x", .intLit 1)]).infer types ctx == none

#guard (Expression.structUpdate (.varRef "p") [("x", .intLit 1)]).infer {} ctx == none

/-- `fun (p : Point) => new Point { x = p.y, y = p.x }` -/
private def swap : FuncDecl where
  docstring := "Swap `p`'s coordinates."
  name := "swap"
  parameters := [("p", .struct "Point")]
  body :=
    .structNew "Point" [("x", .structGet (.varRef "p") "y"), ("y", .structGet (.varRef "p") "x")]
  resultType := .struct "Point"

-- A declaration takes and returns types like any other type, and it is the struct table rather
-- than the globals that has to supply the declaration its parameter names.
#guard (swap.check types []).isOk

#guard !(swap.check {} []).isOk

#guard !(({ swap with resultType := .struct "Pair" } : FuncDecl).check types []).isOk

/-- `fun (p : Point) => { p with x = p.x + 1 }` -/
private def shift : FuncDecl where
  docstring := "Move `p` one step along the x axis."
  name := "shift"
  parameters := [("p", .struct "Point")]
  body := .structUpdate (.varRef "p") [("x", .plus (.structGet (.varRef "p") "x") (.intLit 1))]
  resultType := .struct "Point"

#guard (shift.check types []).isOk

#guard !(shift.check {} []).isOk

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

example : ¬twoXs.FieldNamesUnique := by decide

private def twoXTypes : TypeDecls :=
  { ss := Structs.ofDecls [twoXs] }

-- `structNew` asks for one field per field the declaration lists, so a value of `TwoXs` can be
-- built, and it has to initialize the name twice.  Both at `int`: a field's type is the one its own
-- name resolves to, and the name resolves to the first.
#guard (Expression.structNew "TwoXs" [("x", .intLit 1)]).infer twoXTypes [] == none

#guard
  (Expression.structNew "TwoXs" [("x", .intLit 1), ("x", .intLit 2)]).infer twoXTypes [] ==
    some (.struct "TwoXs")

#guard
  (Expression.structNew "TwoXs" [("x", .intLit 1), ("x", .stringLit "a")]).infer twoXTypes [] ==
    none

-- What is dead is the second field itself, and its declared type with it: every form resolves the
-- name with `List.lookup`, which stops at the first, so the `string` half of `twoXs` is a type
-- nothing is ever held to and the value written for it can never be read back or rebound.
#guard
  (Expression.structGet (.varRef "t") "x").infer twoXTypes [("t", .struct "TwoXs")] == some .int

#guard
  (Expression.structUpdate (.varRef "t") [("x", .stringLit "a")]).infer twoXTypes
      [("t", .struct "TwoXs")] ==
    none

#guard
  (Expression.structUpdate (.varRef "t") [("x", .intLit 1)]).infer twoXTypes
      [("t", .struct "TwoXs")] ==
    some (.struct "TwoXs")

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

#guard
  (Expression.lcons (.varRef "c") (.lnil (.ind "Color"))).infer types ctx ==
    some (.list (.ind "Color"))

#guard (Expression.lcons (.varRef "c") (.lnil (.ind "Hue"))).infer types ctx == none

-- A constructor application gives the type it belongs to, whatever that constructor carries.
#guard (Expression.indNew "Color" "Red" []).infer types ctx == some (.ind "Color")

#guard (Expression.indNew "Shape" "Circle" [.intLit 1]).infer types ctx == some (.ind "Shape")

#guard
  (Expression.indNew "Shape" "Rect" [.varRef "n", .plus (.varRef "n") (.intLit 1)]).infer types
      ctx ==
    some (.ind "Shape")

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

#guard
  (Expression.indNew "Tree" "Node" [.varRef "t", .indNew "Tree" "Leaf" [.intLit 1]]).infer types
      ctx ==
    some (.ind "Tree")

#guard (Expression.indNew "Tree" "Node" [.varRef "t", .intLit 1]).infer types ctx == none

-- A `match` gives the type its alternatives agree on, with each alternative's names bound to what
-- its constructor carries.
#guard
  (Expression.indMatch (.varRef "c")
          [("Red", [], .intLit 0), ("Green", [], .intLit 1), ("Blue", [], .intLit 2)]).infer
      types ctx ==
    some .int

#guard
  (Expression.indMatch (.varRef "sh")
          [("Circle", ["r"], .varRef "r"), ("Rect", ["w", "h"], .plus (.varRef "w") (.varRef "h")),
            ("At", ["q"], .structGet (.varRef "q") "x")]).infer
      types ctx ==
    some .int

#guard
  (Expression.indMatch (.varRef "c")
          [("Red", [], .stringLit "r"), ("Green", [], .stringLit "g"),
            ("Blue", [], .stringLit "b")]).infer
      types ctx ==
    some .string

-- The alternatives may be in any order at all: each one is checked against the constructor it names
-- rather than against the one at its position, so every arrangement of them has the same type.
#guard
  (Expression.indMatch (.varRef "c")
          [("Red", [], .intLit 0), ("Blue", [], .intLit 2), ("Green", [], .intLit 1)]).infer
      types ctx ==
    some .int

#guard
  (Expression.indMatch (.varRef "c")
          [("Blue", [], .intLit 2), ("Green", [], .intLit 1), ("Red", [], .intLit 0)]).infer
      types ctx ==
    some .int

#guard
  (Expression.indMatch (.varRef "c")
          [("Green", [], .stringLit "g"), ("Blue", [], .stringLit "b"),
            ("Red", [], .stringLit "r")]).infer
      types ctx ==
    some .string

-- An alternative out of order binds the names its own constructor declares, at that constructor's
-- data types, rather than those of whichever constructor its position would have paired it with.
#guard
  (Expression.indMatch (.varRef "sh")
          [("Rect", ["w", "h"], .plus (.varRef "w") (.varRef "h")),
            ("At", ["q"], .structGet (.varRef "q") "x"), ("Circle", ["r"], .varRef "r")]).infer
      types ctx ==
    some .int

#guard
  (Expression.indMatch (.varRef "sh")
          [("Rect", ["w", "h"], .varRef "w"), ("At", ["q"], .intLit 0),
            ("Circle", ["r", "r'"], .varRef "r")]).infer
      types ctx ==
    none

#guard
  (Expression.indMatch (.varRef "sh")
          [("At", ["q"], .structGet (.varRef "q") "z"), ("Circle", ["r"], .intLit 0),
            ("Rect", ["w", "h"], .intLit 0)]).infer
      types ctx ==
    none

-- Exhaustive all the same, and no alternative twice or for a constructor the declaration does not
-- have: reordering is all that is permitted.
#guard (Expression.indMatch (.varRef "c") [("Red", [], .intLit 0)]).infer types ctx == none

#guard
  (Expression.indMatch (.varRef "c") [("Blue", [], .intLit 2), ("Green", [], .intLit 1)]).infer
      types ctx ==
    none

#guard
  (Expression.indMatch (.varRef "c")
          [("Red", [], .intLit 0), ("Red", [], .intLit 1), ("Blue", [], .intLit 2)]).infer
      types ctx ==
    none

#guard
  (Expression.indMatch (.varRef "c")
          [("Red", [], .intLit 0), ("Green", [], .intLit 1), ("Blue", [], .intLit 2),
            ("Blue", [], .intLit 3)]).infer
      types ctx ==
    none

#guard
  (Expression.indMatch (.varRef "c")
          [("Red", [], .intLit 0), ("Green", [], .intLit 1), ("Blue", [], .intLit 2),
            ("Purple", [], .intLit 3)]).infer
      types ctx ==
    none

#guard (Expression.indMatch (.varRef "c") []).infer types ctx == none

-- One name per thing the constructor carries, no more and no fewer.
#guard
  (Expression.indMatch (.varRef "sh")
          [("Circle", [], .intLit 0), ("Rect", ["w", "h"], .varRef "w"),
            ("At", ["q"], .intLit 0)]).infer
      types ctx ==
    none

#guard
  (Expression.indMatch (.varRef "sh")
          [("Circle", ["r", "r'"], .varRef "r"), ("Rect", ["w", "h"], .varRef "w"),
            ("At", ["q"], .intLit 0)]).infer
      types ctx ==
    none

-- The names are bound at the types their constructor declares, and at nothing else.
#guard
  (Expression.indMatch (.varRef "sh")
          [("Circle", ["r"], .plus (.varRef "r") (.intLit 1)), ("Rect", ["w", "h"], .varRef "w"),
            ("At", ["q"], .intLit 0)]).infer
      types ctx ==
    some .int

#guard
  (Expression.indMatch (.varRef "sh")
          [("Circle", ["r"], .listReverse (.varRef "r")), ("Rect", ["w", "h"], .varRef "w"),
            ("At", ["q"], .intLit 0)]).infer
      types ctx ==
    none

#guard
  (Expression.indMatch (.varRef "sh")
          [("Circle", ["r"], .intLit 0), ("Rect", ["w", "h"], .intLit 0),
            ("At", ["q"], .structGet (.varRef "q") "z")]).infer
      types ctx ==
    none

-- They are in scope in their own alternative and nowhere else, and they shadow the enclosing
-- context the way a `lam`'s parameters do.
#guard
  (Expression.indMatch (.varRef "sh")
          [("Circle", ["r"], .intLit 0), ("Rect", ["w", "h"], .varRef "r"),
            ("At", ["q"], .intLit 0)]).infer
      types ctx ==
    none

#guard
  (Expression.indMatch (.varRef "sh")
          [("Circle", ["n"], .plus (.varRef "n") (.varRef "n")), ("Rect", ["w", "h"], .varRef "w"),
            ("At", ["q"], .intLit 0)]).infer
      types ctx ==
    some .int

#guard
  (Expression.indMatch (.varRef "sh")
          [("Circle", ["s"], .plus (.varRef "s") (.intLit 1)), ("Rect", ["w", "h"], .varRef "w"),
            ("At", ["q"], .intLit 0)]).infer
      types ctx ==
    some .int

-- Every alternative has to produce the same type, because the match has one type however the value
-- it took apart was built.
#guard
  (Expression.indMatch (.varRef "c")
          [("Red", [], .intLit 0), ("Green", [], .stringLit "g"), ("Blue", [], .intLit 2)]).infer
      types ctx ==
    none

#guard
  (Expression.indMatch (.varRef "c")
          [("Red", [], .varRef "nope"), ("Green", [], .intLit 1), ("Blue", [], .intLit 2)]).infer
      types ctx ==
    none

-- Only a value of a declared inductive type can be taken apart, and the alternatives are the
-- constructors of *its* declaration.
#guard (Expression.indMatch (.varRef "n") [("Red", [], .intLit 0)]).infer types ctx == none

#guard (Expression.indMatch (.varRef "p") [("Red", [], .intLit 0)]).infer types ctx == none

#guard (Expression.indMatch (.varRef "nope") [("Red", [], .intLit 0)]).infer types ctx == none

#guard
  (Expression.indMatch (.varRef "c")
          [("Red", [], .intLit 0), ("Green", [], .intLit 1), ("Blue", [], .intLit 2)]).infer
      {} ctx ==
    none

-- A match is an expression like any other: it can be built out of one and read out of one, and its
-- scrutinee can be anything of the right type.
#guard
  (Expression.plus
          (.indMatch (.indNew "Color" "Red" [])
            [("Red", [], .intLit 0), ("Green", [], .intLit 1), ("Blue", [], .intLit 2)])
          (.intLit 1)).infer
      types ctx ==
    some .int

#guard
  (Expression.indMatch (.varRef "c")
          [("Red", [], .indNew "Shape" "Circle" [.intLit 1]),
            ("Green", [], .indNew "Shape" "Rect" [.intLit 1, .intLit 2]),
            ("Blue", [], .varRef "sh")]).infer
      types ctx ==
    some (.ind "Shape")

/-- `fun (s : Shape) => match s with | Circle(r) => r + r | Rect(w, h) => w + h | At(q) => q.x` -/
private def size : FuncDecl where
  docstring := "How big `s` is, for a rough enough notion of size."
  name := "size"
  parameters := [("s", .ind "Shape")]
  body :=
    .indMatch (.varRef "s")
      [("Circle", ["r"], .plus (.varRef "r") (.varRef "r")),
        ("Rect", ["w", "h"], .plus (.varRef "w") (.varRef "h")),
        ("At", ["q"], .structGet (.varRef "q") "x")]
  resultType := .int

-- A declaration takes and returns an inductive type like any other type, and it is the inductive
-- table that has to supply the declaration its parameter names — `At` also needs the struct table,
-- so `size` checks only against the bundle holding both.
#guard (size.check types []).isOk

#guard !(size.check {} []).isOk

#guard !(size.check { is := Inductives.ofDecls [color, shape, tree] } []).isOk

#guard !(({ size with resultType := .string } : FuncDecl).check types []).isOk

-- The same declaration with its alternatives written in another order is the same declaration as far
-- as checking is concerned, and one of them left out is still not.
#guard
  (({ size with
            body :=
              (Expression.indMatch (.varRef "s")
                [("At", ["q"], .structGet (.varRef "q") "x"),
                  ("Rect", ["w", "h"], .plus (.varRef "w") (.varRef "h")),
                  ("Circle", ["r"], .plus (.varRef "r") (.varRef "r"))]) } :
          FuncDecl).check
      types []).isOk

#guard
  !(({ size with
              body :=
                (Expression.indMatch (.varRef "s")
                  [("At", ["q"], .structGet (.varRef "q") "x"),
                    ("Circle", ["r"], .plus (.varRef "r") (.varRef "r"))]) } :
            FuncDecl).check
        types []).isOk

/-- `fun (n : int) => Shape.Rect(n, n)` -/
private def square : FuncDecl where
  docstring := "A square of side `n`."
  name := "square"
  parameters := [("n", .int)]
  body := .indNew "Shape" "Rect" [.varRef "n", .varRef "n"]
  resultType := .ind "Shape"

#guard (square.check types []).isOk

#guard !(square.check {} []).isOk

#guard !(({ square with resultType := .ind "Color" } : FuncDecl).check types []).isOk

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

example : ¬twoReds.CtorNamesUnique := by decide

private def twoRedTypes : TypeDecls :=
  { is := Inductives.ofDecls [twoReds] }

-- The second `Red` is unreachable: every rule about a constructor resolves it with `List.lookup`,
-- which stops at the first, so the data types the second declares are types nothing can build a
-- value at.
#guard (Expression.indNew "TwoReds" "Red" []).infer twoRedTypes [] == some (.ind "TwoReds")

#guard (Expression.indNew "TwoReds" "Red" [.intLit 1]).infer twoRedTypes [] == none

-- And exhaustiveness counts it all the same, so a match has to write a second alternative for it —
-- one checked against the first `Red`'s data types, and one `Eval` can never reach.
#guard
  (Expression.indMatch (.indNew "TwoReds" "Red" []) [("Red", [], .intLit 0)]).infer twoRedTypes
      [] ==
    none

#guard
  (Expression.indMatch (.indNew "TwoReds" "Red" [])
          [("Red", [], .intLit 0), ("Red", [], .intLit 1)]).infer
      twoRedTypes [] ==
    some .int

#guard
  (Expression.indMatch (.indNew "TwoReds" "Red" [])
          [("Red", [], .intLit 0), ("Red", ["n"], .varRef "n")]).infer
      twoRedTypes [] ==
    none

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

#guard
  (Expression.optionSome (.varRef "f")).infer types ctx == some (.option (.fn [.int, .string] .int))

#guard
  (Expression.optionSome (.plus (.varRef "n") (.intLit 1))).infer types ctx == some (.option .int)

-- And an ill-typed value makes the whole thing ill typed.
#guard (Expression.optionSome (.varRef "nope")).infer types ctx == none

#guard (Expression.optionSome (.plus (.intLit 1) (.stringLit "a"))).infer types ctx == none

-- Options nest, in each other and in everything else: the type former is a type like any other.
#guard
  (Expression.optionSome (.optionSome (.intLit 1))).infer types ctx == some (.option (.option .int))

#guard (Expression.optionSome (.optionNone .int)).infer types ctx == some (.option (.option .int))

#guard
  (Expression.lcons (.varRef "o") (.lnil (.option .int))).infer types ctx ==
    some (.list (.option .int))

#guard (Expression.lcons (.varRef "o") (.lnil (.option .string))).infer types ctx == none

#guard (Expression.optionSome (.varRef "xs")).infer types ctx == some (.option (.list .int))

#guard
  (Expression.lam [("y", .option .int)] (.varRef "y")).infer types ctx ==
    some (.fn [.option .int] (.option .int))

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
#guard
  (Expression.optionMatch (.varRef "o") (.intLit 0) "x" (.varRef "x")).infer types ctx == some .int

#guard
  (Expression.optionMatch (.varRef "o") (.intLit 0) "x" (.plus (.varRef "x") (.intLit 1))).infer
      types ctx ==
    some .int

#guard
  (Expression.optionMatch (.varRef "o") (.boolLit false) "x"
          (.equals (.varRef "x") (.intLit 0))).infer
      types ctx ==
    some .bool

#guard
  (Expression.optionMatch (.varRef "op") (.intLit 0) "q" (.structGet (.varRef "q") "x")).infer types
      ctx ==
    some .int

-- The name is bound at the type the scrutinee's option holds, so using it at another type is ill
-- typed, and it is in scope in the second case alone.
#guard
  (Expression.optionMatch (.varRef "o") (.intLit 0) "x"
          (.plus (.varRef "x") (.stringLit "a"))).infer
      types ctx ==
    none

#guard (Expression.optionMatch (.varRef "op") (.intLit 0) "q" (.varRef "q")).infer types ctx == none

#guard
  (Expression.optionMatch (.varRef "o") (.varRef "x") "x" (.varRef "x")).infer types ctx == none

-- It shadows an enclosing binding of the same name, the way a `let`'s does, and only inside its own
-- case: the first case still sees the outer `n`.
#guard
  (Expression.optionMatch (.optionSome (.stringLit "a")) (.stringLit "b") "n" (.varRef "n")).infer
      types ctx ==
    some .string

#guard
  (Expression.optionMatch (.optionSome (.stringLit "a")) (.varRef "n") "n" (.varRef "n")).infer
      types ctx ==
    none

-- Both cases are held to one type, which is what makes the form have a type at all: neither the
-- value nor the scrutinee says which case will run.
#guard
  (Expression.optionMatch (.varRef "o") (.intLit 0) "x" (.stringLit "a")).infer types ctx == none

#guard
  (Expression.optionMatch (.varRef "o") (.stringLit "a") "x" (.varRef "x")).infer types ctx == none

-- The scrutinee has to be an option, and nothing else will do: there is no value of another type
-- for the two cases to be a case analysis of.
#guard (Expression.optionMatch (.varRef "n") (.intLit 0) "x" (.varRef "x")).infer types ctx == none

#guard (Expression.optionMatch (.varRef "xs") (.intLit 0) "x" (.varRef "x")).infer types ctx == none

#guard (Expression.optionMatch (.varRef "c") (.intLit 0) "x" (.varRef "x")).infer types ctx == none

#guard
  (Expression.optionMatch (.varRef "nope") (.intLit 0) "x" (.varRef "x")).infer types ctx == none

-- An ill-typed case on either side makes the match ill typed, however the other one goes.
#guard
  (Expression.optionMatch (.varRef "o") (.varRef "nope") "x" (.varRef "x")).infer types ctx == none

#guard
  (Expression.optionMatch (.varRef "o") (.intLit 0) "x" (.varRef "nope")).infer types ctx == none

-- A match on an option of options is a match whose bound name is itself an option, which is all
-- nesting comes to.
#guard
  (Expression.optionMatch (.optionSome (.optionSome (.intLit 1))) (.optionNone .int) "x"
          (.varRef "x")).infer
      types ctx ==
    some (.option .int)

-- A match is an expression like any other: it goes where its type goes, and it is an operand of
-- whatever that type is an operand of.
#guard
  (Expression.plus (.optionMatch (.varRef "o") (.intLit 0) "x" (.varRef "x")) (.intLit 1)).infer
      types ctx ==
    some .int

#guard
  (Expression.optionSome (.optionMatch (.varRef "o") (.intLit 0) "x" (.varRef "x"))).infer types
      ctx ==
    some (.option .int)

/-- `fun (o : option int) => match o with | none => 0 | some(x) => x + 1` -/
private def succOr : FuncDecl where
  docstring := "One more than what `o` holds, and `0` when it holds nothing."
  name := "succ-or"
  parameters := [("o", .option .int)]
  body := .optionMatch (.varRef "o") (.intLit 0) "x" (.plus (.varRef "x") (.intLit 1))
  resultType := .int

-- A declaration over the new forms checks like any other, and against no table at all: an option
-- names nothing for a `TypeDecls` to resolve.
#guard (succOr.check {} []).isOk

#guard !(({ succOr with resultType := .option .int } : FuncDecl).check {} []).isOk

#guard !(({ succOr with parameters := [("o", .int)] } : FuncDecl).check {} []).isOk

#guard !(({ succOr with parameters := [("o", .option .string)] } : FuncDecl).check {} []).isOk

/-- `fun (n : int) => some(n)` -/
private def justIt : FuncDecl where
  docstring := "`n`, held in an option."
  name := "just-it"
  parameters := [("n", .int)]
  body := .optionSome (.varRef "n")
  resultType := .option .int

#guard (justIt.check {} []).isOk

#guard !(({ justIt with resultType := .option .string } : FuncDecl).check {} []).isOk

#guard !(({ justIt with resultType := .int } : FuncDecl).check {} []).isOk

/-- `fun => none : int`, which is the shortest declaration that returns an option: the annotation is
the only thing that says which one. -/
private def nothing : FuncDecl where
  docstring := "Nothing, at `int`."
  name := "nothing"
  parameters := []
  body := .optionNone .int
  resultType := .option .int

#guard (nothing.check {} []).isOk

#guard !(({ nothing with resultType := .option .string } : FuncDecl).check {} []).isOk

#guard !(({ nothing with body := Expression.optionNone .string } : FuncDecl).check {} []).isOk

-- Checking agrees with inference on the new forms too.
#guard ((Expression.optionNone .int).check types ctx (.option .int)).isOk

#guard !((Expression.optionNone .int).check types ctx (.option .string)).isOk

#guard !((Expression.optionNone .int).check types ctx .int).isOk

#guard ((Expression.optionSome (.intLit 1)).check types ctx (.option .int)).isOk

#guard !((Expression.optionSome (.intLit 1)).check types ctx .int).isOk

#guard
  ((Expression.optionMatch (.varRef "o") (.intLit 0) "x" (.varRef "x")).check types ctx .int).isOk

/-! ### Hashmaps

A hashmap type relates two types and names no declaration, so it is structural the way `list` and
`option` are and `types` has nothing to say about it.  What is new is the condition every one of the
forms shares: the key type has to be one `Ty.comparable` accepts, since a map is read by comparing
the key it is given against the keys it carries.

`ctx` gives `m` a map from `string` to `int`, `mp` one to a declared struct, `mfn` one to function
type — a comparable key with an uncomparable value, which is allowed — and `mbad` one *from*
function type, which is the case the condition is for. -/

-- A hashmap type is its two halves and nothing else, so two of them agree exactly when both halves
-- do, and the order is part of it.
#guard Ty.hashmap .string .int == Ty.hashmap .string .int

#guard Ty.hashmap .string .int != Ty.hashmap .int .string

#guard Ty.hashmap .string .int != Ty.hashmap .string .string

#guard Ty.hashmap .string .int != Ty.list .string

-- An empty map takes both types from its annotations, the way an empty list takes its one.
#guard (Expression.hashmapEmpty .string .int).infer types ctx == some (.hashmap .string .int)

#guard
  (Expression.hashmapEmpty .int (.list .string)).infer types ctx ==
    some (.hashmap .int (.list .string))

#guard
  (Expression.hashmapEmpty (.struct "Point") .int).infer types ctx ==
    some (.hashmap (.struct "Point") .int)

-- The key type being comparable is the one thing an annotation is held to, and the one way an empty
-- map fails to have a type at all.  A function type is what it rules out, under a declared type as
-- directly.
#guard (Expression.hashmapEmpty (.fn [.int] .int) .int).infer types ctx == none

#guard (Expression.hashmapEmpty (.struct "WithFn") .int).infer types ctx == none

#guard (Expression.hashmapEmpty (.list (.fn [.int] .int)) .int).infer types ctx == none

#guard (Expression.hashmapEmpty (.hashmap .string .int) .int).infer types ctx == none

-- The *value* type is under no such condition: nothing ever compares a value the map holds.
#guard
  (Expression.hashmapEmpty .string (.fn [.int] .int)).infer types ctx ==
    some (.hashmap .string (.fn [.int] .int))

#guard
  (Expression.hashmapEmpty .string (.struct "WithFn")).infer types ctx ==
    some (.hashmap .string (.struct "WithFn"))

#guard
  (Expression.hashmapEmpty .string (.hashmap .string .int)).infer types ctx ==
    some (.hashmap .string (.hashmap .string .int))

-- An annotation names types rather than being checked against the table, so an undeclared name goes
-- through here exactly as it does under `lnil` and `optionNone`.
#guard
  (Expression.hashmapEmpty .string (.struct "Nope")).infer types ctx ==
    some (.hashmap .string (.struct "Nope"))

-- A hashmap is itself never comparable, whatever it relates and however it is wrapped, where a list
-- of the same things is: an association list has no canonical form, so a structural comparison
-- would answer something other than whether two maps are the same map.
#guard !Ty.comparable types (.hashmap .string .int)

#guard !Ty.comparable types (.list (.hashmap .string .int))

#guard !Ty.comparable types (.option (.hashmap .string .int))

#guard Ty.comparable types (.list (.list .string))

#guard (Expression.equals (.varRef "m") (.varRef "m")).infer types ctx == none

#guard (Expression.equals (.varRef "xs") (.varRef "xs")).infer types ctx == some .bool

-- A put keeps the map's type and holds the key and the value to the two halves of it.
#guard
  (Expression.hashmapPut (.varRef "m") (.stringLit "a") (.intLit 1)).infer types ctx ==
    some (.hashmap .string .int)

#guard
  (Expression.hashmapPut (.varRef "m") (.varRef "s") (.varRef "n")).infer types ctx ==
    some (.hashmap .string .int)

#guard
  (Expression.hashmapPut (.varRef "mp") (.varRef "s") (.varRef "p")).infer types ctx ==
    some (.hashmap .string (.struct "Point"))

#guard (Expression.hashmapPut (.varRef "m") (.intLit 1) (.intLit 1)).infer types ctx == none

#guard (Expression.hashmapPut (.varRef "m") (.varRef "s") (.varRef "s")).infer types ctx == none

-- A value of function type is as puttable as any other, since nothing compares one.
#guard
  (Expression.hashmapPut (.varRef "mfn") (.varRef "s") (.lam [("x", .int)] (.varRef "x"))).infer
      types ctx ==
    some (.hashmap .string (.fn [.int] .int))

-- The first operand has to be a map, and nothing else will do.
#guard (Expression.hashmapPut (.varRef "xs") (.stringLit "a") (.intLit 1)).infer types ctx == none

#guard (Expression.hashmapPut (.varRef "p") (.stringLit "a") (.intLit 1)).infer types ctx == none

#guard (Expression.hashmapPut (.varRef "nope") (.stringLit "a") (.intLit 1)).infer types ctx == none

-- A get is the map's value type under an option, so a key the map does not bind is a value rather
-- than an error, and `optionMatch` is what reads the two cases.
#guard (Expression.hashmapGet (.varRef "m") (.stringLit "a")).infer types ctx == some (.option .int)

#guard
  (Expression.hashmapGet (.varRef "mp") (.varRef "s")).infer types ctx ==
    some (.option (.struct "Point"))

#guard
  (Expression.hashmapGet (.varRef "mfn") (.varRef "s")).infer types ctx ==
    some (.option (.fn [.int] .int))

#guard (Expression.hashmapGet (.varRef "m") (.intLit 1)).infer types ctx == none

#guard (Expression.hashmapGet (.varRef "xs") (.stringLit "a")).infer types ctx == none

#guard (Expression.hashmapGet (.varRef "nope") (.stringLit "a")).infer types ctx == none

#guard
  (Expression.optionMatch (.hashmapGet (.varRef "m") (.varRef "s")) (.intLit 0) "x"
          (.varRef "x")).infer
      types ctx ==
    some .int

-- A map whose keys are not comparable is one no form can touch, however well the key and the value
-- fit the two halves of the type it was annotated with.  This is the whole of why the condition is
-- on `put` and `get` as well as on the empty map: a hashmap type reaches a body through a parameter
-- or a field without any `hashmapEmpty` having built one.
#guard
  (Expression.hashmapPut (.varRef "mbad") (.lam [("x", .int)] (.varRef "x")) (.intLit 1)).infer
      types ctx ==
    none

#guard
  (Expression.hashmapGet (.varRef "mbad") (.lam [("x", .int)] (.varRef "x"))).infer types ctx ==
    none

-- A mapping keeps the map's key type and takes its value type from what the function returns, so
-- the function's parameters are the map's two types in that order and the result type is read off
-- its body.
#guard
  (Expression.hashmapMap (.varRef "m") (.lam [("k", .string), ("v", .int)] (.varRef "v"))).infer
      types ctx ==
    some (.hashmap .string .int)

#guard
  (Expression.hashmapMap (.varRef "m")
          (.lam [("k", .string), ("v", .int)] (.plus (.varRef "v") (.intLit 1)))).infer
      types ctx ==
    some (.hashmap .string .int)

#guard
  (Expression.hashmapMap (.varRef "m") (.lam [("k", .string), ("v", .int)] (.varRef "k"))).infer
      types ctx ==
    some (.hashmap .string .string)

#guard
  (Expression.hashmapMap (.varRef "m")
          (.lam [("k", .string), ("v", .int)] (.optionSome (.varRef "v")))).infer
      types ctx ==
    some (.hashmap .string (.option .int))

#guard
  (Expression.hashmapMap (.varRef "mp")
          (.lam [("k", .string), ("v", .struct "Point")] (.structGet (.varRef "v") "x"))).infer
      types ctx ==
    some (.hashmap .string .int)

-- The function takes the key *and* the value, in that order, so one of the wrong arity or with the
-- two the other way round is turned down — the same one comparison `app` makes of an argument list.
#guard
  (Expression.hashmapMap (.varRef "m") (.lam [("v", .int), ("k", .string)] (.varRef "v"))).infer
      types ctx ==
    none

#guard
  (Expression.hashmapMap (.varRef "m") (.lam [("v", .int)] (.varRef "v"))).infer types ctx == none

#guard
  (Expression.hashmapMap (.varRef "m")
          (.lam [("k", .string), ("v", .int), ("z", .int)] (.varRef "v"))).infer
      types ctx ==
    none

#guard (Expression.hashmapMap (.varRef "m") (.varRef "f")).infer types ctx == none

-- Either operand being the wrong kind of thing is enough: the first has to be a map and the second
-- a function.
#guard
  (Expression.hashmapMap (.varRef "xs") (.lam [("k", .string), ("v", .int)] (.varRef "v"))).infer
      types ctx ==
    none

#guard
  (Expression.hashmapMap (.varRef "nope") (.lam [("k", .string), ("v", .int)] (.varRef "v"))).infer
      types ctx ==
    none

#guard (Expression.hashmapMap (.varRef "m") (.varRef "n")).infer types ctx == none

-- A value of function type is as mappable as any other, and as producible: nothing compares a value
-- a map holds, whichever side of the mapping it is on.
#guard
  (Expression.hashmapMap (.varRef "mfn")
          (.lam [("k", .string), ("v", .fn [.int] .int)] (.intLit 1))).infer
      types ctx ==
    some (.hashmap .string .int)

#guard
  (Expression.hashmapMap (.varRef "m")
          (.lam [("k", .string), ("v", .int)] (.lam [("x", .int)] (.varRef "v")))).infer
      types ctx ==
    some (.hashmap .string (.fn [.int] .int))

-- An uncomparable *key* is turned down as it is under the other four forms, even though a mapping
-- compares no key: the keys it carries through are the ones nothing could have done anything with.
#guard
  (Expression.hashmapMap (.varRef "mbad")
          (.lam [("k", .fn [.int] .int), ("v", .int)] (.varRef "v"))).infer
      types ctx ==
    none

-- What it produces is a map like any other, so the forms nest into each other.
#guard
  (Expression.hashmapGet
          (.hashmapMap (.varRef "m") (.lam [("k", .string), ("v", .int)] (.varRef "k")))
          (.varRef "s")).infer
      types ctx ==
    some (.option .string)

#guard
  (Expression.hashmapMap
          (.hashmapMap (.varRef "m") (.lam [("k", .string), ("v", .int)] (.varRef "k")))
          (.lam [("k", .string), ("v", .string)] (.intLit 0))).infer
      types ctx ==
    some (.hashmap .string .int)

#guard
  ((Expression.hashmapMap (.varRef "m") (.lam [("k", .string), ("v", .int)] (.varRef "v"))).check
      types ctx (.hashmap .string .int)).isOk

#guard
  !((Expression.hashmapMap (.varRef "m") (.lam [("k", .string), ("v", .int)] (.varRef "k"))).check
        types ctx (.hashmap .string .int)).isOk

-- A tuple type is the types it lists, in their order, and nothing else.  It is comparable exactly
-- when all of them are: a tuple value is as canonical as a list value, so nothing of the kind that
-- stops two hashmaps being compared is in the way.
#guard Ty.tuple [.string, .int] == Ty.tuple [.string, .int]

#guard Ty.tuple [.string, .int] != Ty.tuple [.int, .string]

#guard Ty.tuple [.string, .int] != Ty.tuple [.string]

#guard Ty.tuple [.string, .int] != Ty.list .string

#guard Ty.comparable types (.tuple [.string, .int])

#guard Ty.comparable types (.tuple [])

#guard Ty.comparable types (.tuple [.string, .struct "Point"])

#guard !Ty.comparable types (.tuple [.string, .fn [.int] .int])

#guard !Ty.comparable types (.tuple [.string, .hashmap .string .int])

#guard !Ty.comparable types (.tuple [.string, .struct "WithFn"])

-- A `toList` is a list of the map's two types as a tuple: one element per binding, the key beside
-- the value it is bound to.  It reads no expression but the map's, so there is no key here for
-- anything to be required of.
#guard
  (Expression.hashmapToList (.varRef "m")).infer types ctx == some (.list (.tuple [.string, .int]))

#guard
  (Expression.hashmapToList (.varRef "mp")).infer types ctx ==
    some (.list (.tuple [.string, .struct "Point"]))

#guard
  (Expression.hashmapToList (.hashmapEmpty .int (.list .string))).infer types ctx ==
    some (.list (.tuple [.int, .list .string]))

-- An uncomparable value type is as fine here as under the other four forms, and an uncomparable key
-- is turned down as it is there — even though converting compares nothing, the way an empty map
-- compares nothing and is held to it too.
#guard
  (Expression.hashmapToList (.varRef "mfn")).infer types ctx ==
    some (.list (.tuple [.string, .fn [.int] .int]))

#guard (Expression.hashmapToList (.varRef "mbad")).infer types ctx == none

-- The operand has to be a map, and nothing else will do.
#guard (Expression.hashmapToList (.varRef "xs")).infer types ctx == none

#guard (Expression.hashmapToList (.varRef "p")).infer types ctx == none

#guard (Expression.hashmapToList (.varRef "nope")).infer types ctx == none

#guard (Expression.hashmapToList (.hashmapGet (.varRef "m") (.varRef "s"))).infer types ctx == none

-- What it produces is an ordinary list, so `reverse` reads one and so does a comparison — which is
-- the one thing the map it came from cannot be read by.  The key and value types being comparable is
-- what that last one needs, and it is exactly what the key half is already held to.
#guard
  (Expression.listReverse (.hashmapToList (.varRef "m"))).infer types ctx ==
    some (.list (.tuple [.string, .int]))

#guard
  (Expression.equals (.hashmapToList (.varRef "m")) (.lnil (.tuple [.string, .int]))).infer types
      ctx ==
    some .bool

#guard
  (Expression.equals (.hashmapToList (.varRef "mfn"))
          (.lnil (.tuple [.string, .fn [.int] .int]))).infer
      types ctx ==
    none

#guard
  ((Expression.hashmapToList (.varRef "m")).check types ctx (.list (.tuple [.string, .int]))).isOk

#guard
  !((Expression.hashmapToList (.varRef "m")).check types ctx (.list (.tuple [.int, .string]))).isOk

/-- `fun (m : hashmap string int) => toList m == [: tuple(string, int)]` -/
private def isEmpty : FuncDecl where
  docstring := "Whether `m` binds nothing."
  name := "is-empty"
  parameters := [("m", .hashmap .string .int)]
  body := .equals (.hashmapToList (.varRef "m")) (.lnil (.tuple [.string, .int]))
  resultType := .bool

-- Converting is what makes this writable at all: a map has no comparison, and the list of its
-- bindings does.
#guard (isEmpty.check {} []).isOk

#guard
  !(({ isEmpty with body := Expression.equals (.varRef "m") (.hashmapEmpty .string .int) } :
            FuncDecl).check
        {} []).isOk

-- The forms nest into each other and into everything else: what each produces is an operand of
-- whatever its type is an operand of.
#guard
  (Expression.hashmapGet (.hashmapPut (.varRef "m") (.varRef "s") (.intLit 1)) (.varRef "s")).infer
      types ctx ==
    some (.option .int)

#guard
  (Expression.hashmapPut (.hashmapPut (.varRef "m") (.stringLit "a") (.intLit 1)) (.stringLit "b")
          (.intLit 2)).infer
      types ctx ==
    some (.hashmap .string .int)

#guard
  (Expression.lcons (.varRef "m") (.lnil (.hashmap .string .int))).infer types ctx ==
    some (.list (.hashmap .string .int))

#guard
  (Expression.optionSome (.varRef "m")).infer types ctx == some (.option (.hashmap .string .int))

#guard
  (Expression.hashmapPut (.hashmapEmpty .string (.hashmap .string .int)) (.varRef "s")
          (.varRef "m")).infer
      types ctx ==
    some (.hashmap .string (.hashmap .string .int))

#guard
  (Expression.lam [("y", .hashmap .string .int)] (.varRef "y")).infer types ctx ==
    some (.fn [.hashmap .string .int] (.hashmap .string .int))

/-- `fun (m : hashmap string int) (k : string) => match m[k] with | none => 0 | some(x) => x` -/
private def getOr : FuncDecl where
  docstring := "What `k` is bound to in `m`, and `0` when it is bound to nothing."
  name := "get-or"
  parameters := [("m", .hashmap .string .int), ("k", .string)]
  body := .optionMatch (.hashmapGet (.varRef "m") (.varRef "k")) (.intLit 0) "x" (.varRef "x")
  resultType := .int

-- A declaration over the new forms checks like any other, and against no table at all: a hashmap
-- names nothing for a `TypeDecls` to resolve.
#guard (getOr.check {} []).isOk

#guard !(({ getOr with resultType := .option .int } : FuncDecl).check {} []).isOk

#guard
  !(({ getOr with parameters := [("m", .hashmap .string .string), ("k", .string)] } :
            FuncDecl).check
        {} []).isOk

#guard
  !(({ getOr with parameters := [("m", .hashmap .int .int), ("k", .string)] } : FuncDecl).check {}
        []).isOk

#guard
  !(({ getOr with parameters := [("m", .list .int), ("k", .string)] } : FuncDecl).check {} []).isOk

/-- `fun (m : hashmap string int) (k : string) (v : int) => { m with [k] = v }` -/
private def bind : FuncDecl where
  docstring := "`m` with `k` bound to `v`."
  name := "bind"
  parameters := [("m", .hashmap .string .int), ("k", .string), ("v", .int)]
  body := .hashmapPut (.varRef "m") (.varRef "k") (.varRef "v")
  resultType := .hashmap .string .int

#guard (bind.check {} []).isOk

#guard !(({ bind with resultType := .hashmap .string .string } : FuncDecl).check {} []).isOk

#guard
  !(({ bind with body := Expression.hashmapPut (.varRef "m") (.varRef "v") (.varRef "k") } :
            FuncDecl).check
        {} []).isOk

-- Checking agrees with inference on the new forms too.
#guard ((Expression.hashmapEmpty .string .int).check types ctx (.hashmap .string .int)).isOk

#guard !((Expression.hashmapEmpty .string .int).check types ctx (.hashmap .int .string)).isOk

#guard
  !((Expression.hashmapEmpty (.fn [.int] .int) .int).check types ctx
        (.hashmap (.fn [.int] .int) .int)).isOk

#guard ((Expression.hashmapGet (.varRef "m") (.varRef "s")).check types ctx (.option .int)).isOk

#guard !((Expression.hashmapGet (.varRef "m") (.varRef "s")).check types ctx .int).isOk

#guard
  ((Expression.hashmapPut (.varRef "m") (.varRef "s") (.varRef "n")).check types ctx
      (.hashmap .string .int)).isOk

/-! ## The two tuple forms

A tuple type carries the types it relates, so neither form resolves a declaration the way the struct
and inductive forms do and neither asks for comparability the way the hashmap forms do.  What is new
is that the result of a read depends on *which* position was read: a tuple is heterogeneous, which
is what makes the index part of the expression rather than something to evaluate.

`ctx` gives `tu` a pair of `string` and `int`, `tu3` a triple, `tue` the empty tuple, and `tufn` a
pair whose second half is a function type — comparable in none of its positions, which is the one
thing a tuple type is held to anywhere. -/

-- Building one takes its type from its elements: as many types as there are elements, each the
-- type of the element in that position.  There is no annotation, and the empty tuple needs none.
#guard
  (Expression.tupleNew [.stringLit "a", .intLit 1]).infer types ctx == some (.tuple [.string, .int])

#guard
  (Expression.tupleNew [.intLit 1, .stringLit "a"]).infer types ctx == some (.tuple [.int, .string])

#guard (Expression.tupleNew []).infer types ctx == some (.tuple [])

#guard (Expression.tupleNew [.intLit 1]).infer types ctx == some (.tuple [.int])

#guard
  (Expression.tupleNew [.varRef "s", .varRef "n", .varRef "flag"]).infer types ctx ==
    some (.tuple [.string, .int, .bool])

#guard
  (Expression.tupleNew [.varRef "p", .varRef "xs"]).infer types ctx ==
    some (.tuple [.struct "Point", .list .int])

-- An element with no type is what makes the whole thing untypeable, the way one argument of a call
-- is: `inferList` stops at the first one it cannot type.
#guard (Expression.tupleNew [.varRef "s", .varRef "nope"]).infer types ctx == none

#guard (Expression.tupleNew [.plus (.varRef "s") (.intLit 1)]).infer types ctx == none

-- A value of function type or of hashmap type is as collectable as any other: nothing here compares
-- an element, so a `tupleNew` is under no condition a `hashmapEmpty` would be.
#guard
  (Expression.tupleNew [.varRef "s", .lam [("x", .int)] (.varRef "x")]).infer types ctx ==
    some (.tuple [.string, .fn [.int] .int])

#guard (Expression.tupleNew [.varRef "m"]).infer types ctx == some (.tuple [.hashmap .string .int])

-- Reading one is the type its tuple type gives at that index, which is what makes a heterogeneous
-- value readable at all.
#guard (Expression.tupleGet (.varRef "tu") 0).infer types ctx == some .string

#guard (Expression.tupleGet (.varRef "tu") 1).infer types ctx == some .int

#guard (Expression.tupleGet (.varRef "tu3") 0).infer types ctx == some .int

#guard (Expression.tupleGet (.varRef "tu3") 1).infer types ctx == some .string

#guard (Expression.tupleGet (.varRef "tu3") 2).infer types ctx == some .bool

#guard (Expression.tupleGet (.varRef "tufn") 1).infer types ctx == some (.fn [.int] .int)

-- An index past the end has no type, and the empty tuple has no index at all: `getElem?` on the
-- type list is the whole of the rule, so this is decided before anything runs.
#guard (Expression.tupleGet (.varRef "tu") 2).infer types ctx == none

#guard (Expression.tupleGet (.varRef "tu3") 3).infer types ctx == none

#guard (Expression.tupleGet (.varRef "tue") 0).infer types ctx == none

-- The operand has to be a tuple, and nothing else will do — a list of the same things included,
-- which is the one type a tuple is otherwise easy to mistake for.
#guard (Expression.tupleGet (.varRef "xs") 0).infer types ctx == none

#guard (Expression.tupleGet (.varRef "p") 0).infer types ctx == none

#guard (Expression.tupleGet (.varRef "m") 0).infer types ctx == none

#guard (Expression.tupleGet (.varRef "nope") 0).infer types ctx == none

-- The two forms nest into each other and into everything else: what each produces is an operand of
-- whatever its type is an operand of.
#guard (Expression.tupleGet (.tupleNew [.varRef "s", .varRef "n"]) 1).infer types ctx == some .int

#guard
  (Expression.tupleNew [.tupleNew [.intLit 1], .varRef "s"]).infer types ctx ==
    some (.tuple [.tuple [.int], .string])

#guard
  (Expression.tupleGet (.tupleGet (.tupleNew [.varRef "tu"]) 0) 0).infer types ctx == some .string

#guard (Expression.plus (.tupleGet (.varRef "tu") 1) (.intLit 1)).infer types ctx == some .int

#guard
  (Expression.lcons (.varRef "tu") (.lnil (.tuple [.string, .int]))).infer types ctx ==
    some (.list (.tuple [.string, .int]))

#guard
  (Expression.structGet (.tupleGet (.tupleNew [.varRef "p"]) 0) "x").infer types ctx == some .int

-- A tuple is comparable exactly when every position is, so a pair of a hashmap is not and the pair
-- `toList` produces is: what stops two maps being compared is the order their bindings are carried
-- in, and a list of pairs compared elementwise answers about that order rather than in spite of it.
#guard (Expression.equals (.varRef "tu") (.varRef "tu")).infer types ctx == some .bool

#guard (Expression.equals (.varRef "tue") (.varRef "tue")).infer types ctx == some .bool

#guard (Expression.equals (.varRef "tufn") (.varRef "tufn")).infer types ctx == none

#guard
  (Expression.equals (.tupleNew [.varRef "m"]) (.tupleNew [.varRef "m"])).infer types ctx == none

#guard
  (Expression.equals (.hashmapToList (.varRef "m")) (.tupleNew [.varRef "s", .varRef "n"])).infer
      types ctx ==
    none

#guard
  (Expression.equals (.hashmapToList (.varRef "m"))
          (.lcons (.tupleNew [.varRef "s", .varRef "n"]) (.lnil (.tuple [.string, .int])))).infer
      types ctx ==
    some .bool

/-- `fun (m : hashmap string int) (k : string) => tuple(m, k).0[tuple(m, k).1]` written the long
way: a declaration whose body builds a tuple and reads both halves back out. -/
private def roundTrip : FuncDecl where
  docstring := "What `k` is bound to in `m`, by way of a tuple holding both."
  name := "round-trip"
  parameters := [("m", .hashmap .string .int), ("k", .string)]
  body :=
    .let_ "pair" (.tupleNew [.varRef "m", .varRef "k"])
      (.hashmapGet (.tupleGet (.varRef "pair") 0) (.tupleGet (.varRef "pair") 1))
  resultType := .option .int

-- A declaration over the new forms checks like any other, and against no table at all: a tuple
-- names nothing for a `TypeDecls` to resolve.
#guard (roundTrip.check {} []).isOk

#guard !(({ roundTrip with resultType := .int } : FuncDecl).check {} []).isOk

#guard
  !(({ roundTrip with
              body :=
                .let_ "pair" (.tupleNew [.varRef "k", .varRef "m"])
                  (.hashmapGet (.tupleGet (.varRef "pair") 0) (.tupleGet (.varRef "pair") 1)) } :
            FuncDecl).check
        {} []).isOk

-- Checking agrees with inference on the tuple forms too.
#guard
  ((Expression.tupleNew [.varRef "s", .varRef "n"]).check types ctx (.tuple [.string, .int])).isOk

#guard
  !((Expression.tupleNew [.varRef "s", .varRef "n"]).check types ctx (.tuple [.int, .string])).isOk

#guard !((Expression.tupleNew [.varRef "s", .varRef "n"]).check types ctx (.tuple [.string])).isOk

#guard ((Expression.tupleGet (.varRef "tu") 0).check types ctx .string).isOk

#guard !((Expression.tupleGet (.varRef "tu") 0).check types ctx .int).isOk

/-! ## Unreachable branches

The one form under no condition at all: its annotation is its type, whatever that annotation is and
whatever is in scope.  What there is to test is therefore not what it accepts but where it can
stand — on a branch whose siblings settled a type it then has to agree with. -/

-- Its annotation is its type, with nothing asked of the context and no type turned down: a function
-- type and a hashmap type are as good as an `int` here, unlike at `hashmapEmpty`'s key.
#guard (Expression.unreachable .int "nope").infer types ctx == some .int

#guard (Expression.unreachable (.struct "Point") "nope").infer types ctx == some (.struct "Point")

#guard (Expression.unreachable (.fn [.int] .int) "nope").infer types ctx == some (.fn [.int] .int)

#guard
  (Expression.unreachable (.hashmap (.fn [.int] .int) .int) "nope").infer types ctx ==
    some (.hashmap (.fn [.int] .int) .int)

-- A type no declaration declares is not turned down either: nothing resolves it, because nothing
-- evaluates the expression it annotates.
#guard (Expression.unreachable (.struct "Nope") "nope").infer types ctx == some (.struct "Nope")

#guard (Expression.unreachable .int "nope").infer {} [] == some .int

-- On a branch it has to agree with the branch's type, which is the whole of what the annotation is
-- for: an `if` is typeable exactly when the annotation is what the other branch came out as.
#guard
  (Expression.ite (.varRef "flag") (.varRef "n") (.unreachable .int "nope")).infer types ctx ==
    some .int

#guard
  (Expression.ite (.varRef "flag") (.unreachable .int "nope") (.varRef "n")).infer types ctx ==
    some .int

#guard
  (Expression.ite (.varRef "flag") (.varRef "s") (.unreachable .int "nope")).infer types ctx == none

-- Both branches unreachable is typeable too, and still only at one type.
#guard
  (Expression.ite (.varRef "flag") (.unreachable .int "a") (.unreachable .int "b")).infer types
      ctx ==
    some .int

#guard
  (Expression.ite (.varRef "flag") (.unreachable .int "a") (.unreachable .string "b")).infer types
      ctx ==
    none

-- The same on a match's alternatives, where the common type is found among all of them rather than
-- between two, and in a case of an option match.
#guard
  (Expression.indMatch (.varRef "c")
          [("Red", [], .intLit 0), ("Green", [], .unreachable .int "nope"),
            ("Blue", [], .intLit 1)]).infer
      types ctx ==
    some .int

#guard
  (Expression.indMatch (.varRef "c")
          [("Red", [], .intLit 0), ("Green", [], .unreachable .string "nope"),
            ("Blue", [], .intLit 1)]).infer
      types ctx ==
    none

#guard
  (Expression.optionMatch (.varRef "o") (.unreachable .int "nope") "x" (.varRef "x")).infer types
      ctx ==
    some .int

-- Elsewhere it stands wherever a value of its annotation would: an operand, an argument, a field.
#guard (Expression.plus (.varRef "n") (.unreachable .int "nope")).infer types ctx == some .int

#guard (Expression.plus (.varRef "n") (.unreachable .string "nope")).infer types ctx == none

#guard
  (Expression.app (.varRef "f") [.unreachable .int "nope", .varRef "s"]).infer types ctx ==
    some .int

#guard
  (Expression.structNew "Point" [("x", .unreachable .int "nope"), ("y", .intLit 2)]).infer types
      ctx ==
    some (.struct "Point")

/-- A declaration whose body has a branch nothing reaches, which is the shape the form is for: the
`else` is where the subtraction would have gone negative, and the type checker asks only that it be
annotated `int` like the branch beside it. -/
private def pred : FuncDecl where
  docstring := ""
  name := "pred"
  parameters := [("n", .int)]
  body :=
    .ite (.lt (.intLit 0) (.varRef "n")) (.minus (.varRef "n") (.intLit 1))
      (.unreachable .int "n is positive")
  resultType := .int

#guard (pred.check {} []).isOk

#guard !(({ pred with resultType := .string } : FuncDecl).check {} []).isOk

-- Checking agrees with inference, as it does everywhere: the form determines its own type, so
-- checking it against any other type fails.
#guard ((Expression.unreachable .int "nope").check types ctx .int).isOk

#guard !((Expression.unreachable .int "nope").check types ctx .string).isOk

/-! ### Messages

What a check that did not pass says about it.  Everything above asks only whether a program checks,
which is what the rest of the development is stated over; these are about the other half of the
answer.

Two things make up a message: the rule that turned an expression down, and the path the expression
was reached by.  The rule is the innermost one that failed — a nest of forms reports the one
subexpression nothing could be done with, not the whole of it — and the path is what each enclosing
form adds on the way back out, a field or an alternative or a declaration at a time. -/

/-- The message a check reported, or `"ok"` where it reported none.

`Except.isOk` is what the guards above ask, since none of them is about a message; this is what the
ones below compare. -/
private def message (r : Except String Unit) : String :=
  match r with
  | .ok _ => "ok"
  | .error m => m

-- A name nothing in scope has, which is the one failure no type can be read off at all.
#guard
  message ((Expression.varRef "nope").check types ctx .int) ==
    "no variable named 'nope' is in scope"

-- An operand of the wrong type is reported at the position it was in, with both types named.
#guard
  message ((Expression.plus (.varRef "s") (.intLit 1)).check types ctx .int) ==
    "the left operand of `+` has type string where int was expected"

#guard
  message ((Expression.plus (.intLit 1) (.varRef "s")).check types ctx .int) ==
    "the right operand of `+` has type string where int was expected"

#guard
  message ((Expression.ite (.varRef "n") (.intLit 1) (.intLit 2)).check types ctx .int) ==
    "the condition of an `if` has type int where bool was expected"

#guard
  message ((Expression.ite (.varRef "flag") (.intLit 1) (.varRef "s")).check types ctx .int) ==
    "the `else` branch of an `if` has type string where int was expected"

-- An expression that is well typed at a type other than the expected one is the one failure
-- `Expression.check` reports itself, rather than passing along what inference found.
#guard
  message ((Expression.intLit 1).check types ctx .string) ==
    "this expression has type int where string was expected"

-- A call reports its arity and the position of a mismatched argument separately: `Ty.fn` records
-- every parameter at once, so too few arguments is a different thing to say than a wrong one.
#guard
  message ((Expression.app (.varRef "f") [.intLit 1]).check types ctx .int) ==
    "this call takes 2 argument(s), but was given 1"

#guard
  message ((Expression.app (.varRef "f") [.intLit 1, .intLit 2]).check types ctx .int) ==
    "argument 2 of this call has type int where string was expected"

#guard
  message ((Expression.app (.varRef "n") [.intLit 1]).check types ctx .int) ==
    "a call needs a function, but what is applied here has type int"

-- A form that needs a particular kind of operand names the kind and the type it was given.
#guard
  message ((Expression.listLength (.varRef "n")).check types ctx .int) ==
    "`length` needs a list, but its operand has type int"

#guard
  message
      ((Expression.listMap (.varRef "xs") (.lam [("x", .string)] (.varRef "x"))).check types ctx
        (.list .string)) ==
    "`map list` over a list of int needs a function of one int parameter, \
      but this one takes (string)"

#guard
  message
      ((Expression.listFlatMap (.varRef "xs") (.lam [("x", .string)] (.lnil .int))).check types ctx
        (.list .int)) ==
    "`flatMap` over a list of int needs a function of one int parameter, \
      but this one takes (string)"

-- And the condition that separates it from a mapping says what the function returned, since what is
-- wrong with returning something other than a list is that type and nothing the shape shows.
#guard
  message
      ((Expression.listFlatMap (.varRef "xs") (.lam [("x", .int)] (.varRef "x"))).check types ctx
        (.list .int)) ==
    "`flatMap` concatenates what its function returns, so that must be a list, \
      but this one returns int"

#guard
  message
      ((Expression.listSortOn (.varRef "xs") (.lam [("x", .string)] (.varRef "x"))).check types ctx
        (.list .int)) ==
    "`sortOn` over a list of int needs a projection taking one int parameter, \
      but this one takes (string)"

-- And the one condition no other list form has says what the key's type was, since a key that
-- cannot be ordered is nothing the shape of the expression shows.
#guard
  message
      ((Expression.listSortOn (.varRef "xs") (.lam [("x", .int)] (.varRef "c"))).check types ctx
        (.list .int)) ==
    "a sort key must be a type with an ordering, but this projection returns inductive Color, \
      which cannot be ordered"

-- A comparison's arity is reported the way a projection's is, with the element type named twice:
-- there is one parameter per element it is asked about.
#guard
  message
      ((Expression.listSortBy (.varRef "xs") (.lam [("x", .int)] (.boolLit true))).check types ctx
        (.list .int)) ==
    "`sortBy` over a list of int needs a comparison taking two int parameters, \
      but this one takes (int)"

-- And its result is the condition that takes the place of `sortOn`'s on the key: the answer is the
-- ordering here, so what is wrong with a comparison returning something else is what it returned.
#guard
  message
      ((Expression.listSortBy (.varRef "xs")
            (.lam [("a", .int), ("b", .int)] (.plus (.varRef "a") (.varRef "b")))).check types ctx
        (.list .int)) ==
    "a comparison must answer whether one element comes first, but this one returns int \
      rather than a bool"

-- A predicate's arity is reported with the element type named once, where a comparison's names it
-- twice: one parameter per element it is asked about, and a search asks about one.
#guard
  message
      ((Expression.listFindIndex (.varRef "xs") (.lam [("x", .string)] (.boolLit true))).check
        types ctx (.option .int)) ==
    "`findIndex` over a list of int needs a predicate taking one int parameter, \
      but this one takes (string)"

-- And its result is held to a `bool` the way a comparison's is, with what it answered named: there
-- is nothing about the shape of the expression that shows it.
#guard
  message
      ((Expression.listFindIndex (.varRef "xs") (.lam [("x", .int)] (.varRef "x"))).check types ctx
        (.option .int)) ==
    "a predicate must answer whether an element matches, but this one returns int \
      rather than a bool"

#guard
  message ((Expression.hashmapGet (.varRef "n") (.stringLit "k")).check types ctx (.option .int)) ==
    "`m[k]` needs a hashmap, but what is looked up in here has type int"

#guard
  message ((Expression.tupleGet (.varRef "tu") 5).check types ctx .int) ==
    "a tuple of type tuple(string, int) has no element at index 5"

-- The struct forms report the declaration and the field, whichever of the two is wrong.
#guard
  message
      ((Expression.structNew "Pointe" [("x", .intLit 1), ("y", .intLit 2)]).check types ctx
        (.struct "Pointe")) ==
    "no struct named 'Pointe' is declared"

#guard
  message ((Expression.structNew "Point" [("x", .intLit 1)]).check types ctx (.struct "Point")) ==
    "struct 'Point' is missing field 'y'"

#guard
  message
      ((Expression.structNew "Point" [("x", .intLit 1), ("y", .stringLit "a")]).check types ctx
        (.struct "Point")) ==
    "field 'y' of struct 'Point' has type int, but was given string"

#guard
  message
      ((Expression.structNew "Point" [("x", .intLit 1), ("z", .intLit 2)]).check types ctx
        (.struct "Point")) ==
    "struct 'Point' has no field named 'z'"

#guard
  message ((Expression.structGet (.varRef "p") "z").check types ctx .int) ==
    "struct 'Point' has no field named 'z'"

#guard
  message ((Expression.structGet (.varRef "n") "x").check types ctx .int) ==
    "a field read needs a struct, but what is read here has type int"

#guard
  message ((Expression.structUpdate (.varRef "p") []).check types ctx (.struct "Point")) ==
    "a struct update must rebind at least one field of struct 'Point'"

-- An inductive type's forms report the declaration and the constructor the same way, and a match
-- reports the constructor it has no alternative for and the types it could not reconcile.
#guard
  message ((Expression.indNew "Shape" "Square" [.intLit 1]).check types ctx (.ind "Shape")) ==
    "inductive 'Shape' has no constructor named 'Square'"

#guard
  message
      ((Expression.indNew "Shape" "Circle" [.intLit 1, .intLit 2]).check types ctx
        (.ind "Shape")) ==
    "constructor 'Circle' of inductive 'Shape' takes 1 argument(s), but was given 2"

#guard
  message ((Expression.indMatch (.varRef "c") [("Red", [], .intLit 0)]).check types ctx .int) ==
    "this match has no alternative for constructor 'Green' of inductive 'Color'"

#guard
  message
      ((Expression.indMatch (.varRef "c")
            [("Red", [], .intLit 0), ("Green", [], .varRef "s"), ("Blue", [], .intLit 1)]).check
        types ctx .int) ==
    "the alternatives of this match have types int, string, int, which differ"

#guard
  message
      ((Expression.indMatch (.varRef "sh")
            [("Circle", ["r", "q"], .varRef "r"), ("Rect", ["w", "h"], .varRef "w"),
              ("At", ["q"], .intLit 0)]).check
        types ctx .int) ==
    "the alternative for 'Circle' binds 2 name(s), but 'Circle' carries 1 value(s)"

#guard
  message ((Expression.indMatch (.varRef "n") [("Red", [], .intLit 0)]).check types ctx .int) ==
    "a match needs a value of an inductive type, but its scrutinee has type int"

-- A type no comparison reaches the bottom of is reported where it is asked for, which is the one
-- condition no shape of expression could have shown.
#guard
  message ((Expression.equals (.varRef "f") (.varRef "f")).check types ctx .bool) ==
    "values of type (int, string) -> int cannot be compared, so `==` does not apply to them"

#guard
  message ((Expression.lt (.varRef "flag") (.boolLit true)).check types ctx .bool) ==
    "values of type bool cannot be ordered, so `<` does not apply to them"

#guard
  message ((Expression.le (.varRef "p") (.varRef "p")).check types ctx .bool) ==
    "values of type struct Point cannot be ordered, so `<=` does not apply to them"

#guard
  message ((Expression.lt (.intLit 1) (.varRef "s")).check types ctx .bool) ==
    "the right operand of `<` has type string where int was expected"

#guard
  message
      ((Expression.hashmapEmpty (.fn [.int] .int) .int).check types ctx
        (.hashmap (.fn [.int] .int) .int)) ==
    "(int) -> int cannot be a hashmap's key type, since values of it cannot be compared"

-- A failure inside a field or an alternative keeps the path it was reached by.
#guard
  message
      ((Expression.structNew "Point" [("x", .intLit 1), ("y", .varRef "nope")]).check types ctx
        (.struct "Point")) ==
    "in field 'y': no variable named 'nope' is in scope"

#guard
  message
      ((Expression.indMatch (.varRef "c")
            [("Red", [], .varRef "nope"), ("Green", [], .intLit 0), ("Blue", [], .intLit 1)]).check
        types ctx .int) ==
    "in the alternative for 'Red': no variable named 'nope' is in scope"

-- A declaration names itself, and a table or a program reports the first entry that did not check.
#guard
  message (({ addPred with resultType := .list .int } : FuncDecl).check {} []) ==
    "in the body of 'add-pred': this expression has type int where list int was expected"

#guard
  message (Globals.check {} (Globals.ofDecls [{ addPred with resultType := .list .int }, bang])) ==
    "in the body of 'add-pred': this expression has type int where list int was expected"

#guard
  message (({ funcDecls := [{ addPred with resultType := .list .int }] } : Program).check) ==
    "in the body of 'add-pred': this expression has type int where list int was expected"

-- A program is turned down for a declaration that names a field or a constructor twice before any
-- of its bodies are looked at, so that is what a message about one says.
#guard
  message (({ funcDecls := [addPred], structDecls := [twoXs] } : Program).check) ==
    "struct 'TwoXs' declares the field 'x' twice"

#guard
  message (({ funcDecls := [addPred], inductiveDecls := [twoReds] } : Program).check) ==
    "inductive 'TwoReds' declares the constructor 'Red' twice"

-- An `unreachable` imposes no condition of its own, so the only thing that can go wrong with one is
-- that the type it was written with is not the type wanted where it stands — which is what every
-- expression's message says and not one of this form's.
#guard
  message ((Expression.unreachable .int "nope").check types ctx .string) ==
    "this expression has type int where string was expected"

#guard
  message
      ((Expression.ite (.varRef "flag") (.varRef "s") (.unreachable .int "nope")).check types ctx
        .string) ==
    "the `else` branch of an `if` has type int where string was expected"
