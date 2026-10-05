module

import LgtmDeepLean.Lang.Syntax
meta import LgtmDeepLean.Lang.Syntax

/-! # Tests for the surface syntax

What `[lgtm_ty| ...]`, `[lgtm| ...]`, `lgtm def`, `lgtm struct`, and `lgtm inductive` elaborate to:
each form against the constructors it describes, the precedences that decide how a term without
parentheses is read, and the declarations the commands build — checked, where it is the point, with
`FuncDecl.check`. -/

-- Types elaborate to the constructors they describe, `fn` taking all its parameters at once.
example : [lgtm_ty| int] = Ty.int := rfl
example : [lgtm_ty| bool] = Ty.bool := rfl
example : [lgtm_ty| list bool] = Ty.list .bool := rfl
example : [lgtm_ty| (bool, int) -> bool] = Ty.fn [.bool, .int] .bool := rfl
example : [lgtm_ty| list string] = Ty.list .string := rfl
example : [lgtm_ty| list list int] = Ty.list (.list .int) := rfl
example : [lgtm_ty| (int, string) -> int] = Ty.fn [.int, .string] .int := rfl
example : [lgtm_ty| () -> int] = Ty.fn [] .int := rfl
example : [lgtm_ty| list ((int) -> int)] = Ty.list (.fn [.int] .int) := rfl
example : [lgtm_ty| (int) -> (string) -> int] = Ty.fn [.int] (.fn [.string] .int) := rfl

-- Leaves.
example : [lgtm| x] = Expression.varRef "x" := rfl
example : [lgtm| var "my-var"] = Expression.varRef "my-var" := rfl
example : [lgtm| 3] = Expression.intLit 3 := rfl
example : [lgtm| "hi"] = Expression.stringLit "hi" := rfl
example : [lgtm| true] = Expression.boolLit true := rfl
example : [lgtm| false] = Expression.boolLit false := rfl

-- `true` and `false` are keywords, so neither is a variable name inside a DSL term.  Outside one
-- they are Lean's own `true` and `false`, which declaring them with `&` is what preserves.
example : [lgtm| var "true"] = Expression.varRef "true" := rfl
example : (true : Bool) = Bool.true := rfl

-- A `bool` literal is an ordinary operand: it goes in a list, in a call, and in a conditional.
example : [lgtm| [true, false : bool]]
    = Expression.lcons (.boolLit true) (.lcons (.boolLit false) (.lnil .bool)) := rfl
example : [lgtm| f(true, 1)] = Expression.app (.varRef "f") [.boolLit true, .intLit 1] := rfl
example : [lgtm| true :: bs] = Expression.lcons (.boolLit true) (.varRef "bs") := rfl
example : [lgtm| let b = true in b]
    = Expression.let_ "b" (.boolLit true) (.varRef "b") := rfl
example : [lgtm| fun (b : bool) => true]
    = Expression.lam [("b", .bool)] (.boolLit true) := rfl

-- Arithmetic is left-associative, and parentheses group as written.
example : [lgtm| x + 1] = Expression.plus (.varRef "x") (.intLit 1) := rfl
example : [lgtm| x + y - 1]
    = Expression.minus (.plus (.varRef "x") (.varRef "y")) (.intLit 1) := rfl
example : [lgtm| x + (y - 1)]
    = Expression.plus (.varRef "x") (.minus (.varRef "y") (.intLit 1)) := rfl

-- `::` binds looser than `+`, so the arithmetic happens to the element rather than the list.
example : [lgtm| x :: xs] = Expression.lcons (.varRef "x") (.varRef "xs") := rfl
example : [lgtm| x + 1 :: xs]
    = Expression.lcons (.plus (.varRef "x") (.intLit 1)) (.varRef "xs") := rfl

-- `==` is looser than both, so each of its operands is as much as can be read before it.
example : [lgtm| x == y] = Expression.equals (.varRef "x") (.varRef "y") := rfl
example : [lgtm| x + 1 == y]
    = Expression.equals (.plus (.varRef "x") (.intLit 1)) (.varRef "y") := rfl
example : [lgtm| x :: xs == ys]
    = Expression.equals (.lcons (.varRef "x") (.varRef "xs")) (.varRef "ys") := rfl
example : [lgtm| reverse xs == ys]
    = Expression.equals (.listReverse (.varRef "xs")) (.varRef "ys") := rfl
example : [lgtm| f(1) == g(2)]
    = Expression.equals (.app (.varRef "f") [.intLit 1]) (.app (.varRef "g") [.intLit 2]) := rfl
example : [lgtm| p.x == q.x]
    = Expression.equals (.structGet (.varRef "p") "x") (.structGet (.varRef "q") "x") := rfl

-- Parentheses are what chain comparisons, since `==` is non-associative; and a comparison is an
-- operand anywhere a `bool` is one.
example : [lgtm| (x == y) == b]
    = Expression.equals (.equals (.varRef "x") (.varRef "y")) (.varRef "b") := rfl
example : [lgtm| if x == y then { 1 } else { 2 }]
    = Expression.ite (.equals (.varRef "x") (.varRef "y")) (.intLit 1) (.intLit 2) := rfl
example : [lgtm| let e = x == y in e]
    = Expression.let_ "e" (.equals (.varRef "x") (.varRef "y")) (.varRef "e") := rfl
example : [lgtm| fun (q : int) => q == n]
    = Expression.lam [("q", .int)] (.equals (.varRef "q") (.varRef "n")) := rfl
example : [lgtm| f(x == y)]
    = Expression.app (.varRef "f") [.equals (.varRef "x") (.varRef "y")] := rfl
example : [lgtm| [x == y, true : bool]]
    = Expression.lcons (.equals (.varRef "x") (.varRef "y"))
        (.lcons (.boolLit true) (.lnil .bool)) := rfl

-- A list literal is right-nested `lcons` onto the `lnil` its annotation gives.
example : [lgtm| [: int]] = Expression.lnil .int := rfl
example : [lgtm| [1 : int]] = Expression.lcons (.intLit 1) (.lnil .int) := rfl
example : [lgtm| ["!", s : string]]
    = Expression.lcons (.stringLit "!") (.lcons (.varRef "s") (.lnil .string)) := rfl

-- `reverse` is a form of its own, not a call, so it takes its operand without parentheses.
example : [lgtm| reverse xs] = Expression.listReverse (.varRef "xs") := rfl
example : [lgtm| reverse (x :: xs)]
    = Expression.listReverse (.lcons (.varRef "x") (.varRef "xs")) := rfl
example : [lgtm| reverse reverse xs]
    = Expression.listReverse (.listReverse (.varRef "xs")) := rfl

-- Application takes all its arguments at once, and nests to the left.
example : [lgtm| f(x)] = Expression.app (.varRef "f") [.varRef "x"] := rfl
example : [lgtm| f(1, "a")] = Expression.app (.varRef "f") [.intLit 1, .stringLit "a"] := rfl
example : [lgtm| f()] = Expression.app (.varRef "f") [] := rfl
example : [lgtm| f(1)(2)]
    = Expression.app (.app (.varRef "f") [.intLit 1]) [.intLit 2] := rfl

-- A `lam`'s parameters are IR names paired with their annotations.
example : [lgtm| fun (x : int) => x]
    = Expression.lam [("x", .int)] (.varRef "x") := rfl
example : [lgtm| fun (x : int) (y : string) => y]
    = Expression.lam [("x", .int), ("y", .string)] (.varRef "y") := rfl
example : [lgtm| fun => 1] = Expression.lam [] (.intLit 1) := rfl

-- A lambda's body extends as far right as it can, so the `+` is inside it.
example : [lgtm| fun (x : int) => x + 1]
    = Expression.lam [("x", .int)] (.plus (.varRef "x") (.intLit 1)) := rfl

-- A `let` names the expression it binds, which carries no annotation.
example : [lgtm| let x = 1 in x] = Expression.let_ "x" (.intLit 1) (.varRef "x") := rfl
example : [lgtm| let x = y + 1 in x + x]
    = Expression.let_ "x" (.plus (.varRef "y") (.intLit 1))
        (.plus (.varRef "x") (.varRef "x")) := rfl

-- The body extends as far right as it can, so `let`s chain without parentheses and a `let` inside a
-- lambda swallows the rest of the body.
example : [lgtm| let x = 1 in let y = 2 in x + y]
    = Expression.let_ "x" (.intLit 1) (.let_ "y" (.intLit 2)
        (.plus (.varRef "x") (.varRef "y"))) := rfl
example : [lgtm| fun (n : int) => let m = n + 1 in m + m]
    = Expression.lam [("n", .int)] (.let_ "m" (.plus (.varRef "n") (.intLit 1))
        (.plus (.varRef "m") (.varRef "m"))) := rfl

-- The bound expression stops at `in`, so a `fun` or a call on the right of the `=` needs no
-- parentheses either.
example : [lgtm| let f = fun (x : int) => x in f(1)]
    = Expression.let_ "f" (.lam [("x", .int)] (.varRef "x"))
        (.app (.varRef "f") [.intLit 1]) := rfl
example : [lgtm| let xs = reverse ys in x :: xs]
    = Expression.let_ "xs" (.listReverse (.varRef "ys"))
        (.lcons (.varRef "x") (.varRef "xs")) := rfl

-- Parenthesizing the body is what puts something after the `let` rather than inside it.
example : [lgtm| (let x = 1 in x) + 2]
    = Expression.plus (.let_ "x" (.intLit 1) (.varRef "x")) (.intLit 2) := rfl

-- A conditional is its condition and its two braced branches.
example : [lgtm| if b then { 1 } else { 2 }]
    = Expression.ite (.varRef "b") (.intLit 1) (.intLit 2) := rfl
example : [lgtm| if true then { 1 } else { 2 }]
    = Expression.ite (.boolLit true) (.intLit 1) (.intLit 2) := rfl
example : [lgtm| if b then { true } else { false }]
    = Expression.ite (.varRef "b") (.boolLit true) (.boolLit false) := rfl
example : [lgtm| if f(x) then { x + 1 } else { x - 1 }]
    = Expression.ite (.app (.varRef "f") [.varRef "x"])
        (.plus (.varRef "x") (.intLit 1)) (.minus (.varRef "x") (.intLit 1)) := rfl

-- The braces end the branches, so a conditional is an ordinary operand: the `+ 1` below applies to
-- the whole of it rather than to its second branch, and neither branch needs parentheses.
example : [lgtm| if b then { 1 } else { 2 } + 1]
    = Expression.plus (.ite (.varRef "b") (.intLit 1) (.intLit 2)) (.intLit 1) := rfl
example : [lgtm| if b then { let x = 1 in x } else { match c with | Red => 0 }]
    = Expression.ite (.varRef "b") (.let_ "x" (.intLit 1) (.varRef "x"))
        (.indMatch (.varRef "c") [("Red", [], .intLit 0)]) := rfl
example : [lgtm| f(if b then { 1 } else { 2 })]
    = Expression.app (.varRef "f") [.ite (.varRef "b") (.intLit 1) (.intLit 2)] := rfl

-- And conditionals nest, in the branches and in the condition alike.
example : [lgtm| if b then { if c then { 1 } else { 2 } } else { 3 }]
    = Expression.ite (.varRef "b") (.ite (.varRef "c") (.intLit 1) (.intLit 2)) (.intLit 3) := rfl
example : [lgtm| if if b then { c } else { d } then { 1 } else { 2 }]
    = Expression.ite (.ite (.varRef "b") (.varRef "c") (.varRef "d"))
        (.intLit 1) (.intLit 2) := rfl

-- Identifiers are IR names, never Lean ones: `n` below is a `varRef`, not this Lean `n`.
private def n : Expression := .intLit 99
example : [lgtm| n] = Expression.varRef "n" := rfl

-- Splicing is how a Lean term gets in.
example : [lgtm| ~(n) + 1] = Expression.plus (.intLit 99) (.intLit 1) := rfl
example : [lgtm_ty| list ~(Ty.int)] = Ty.list .int := rfl

/-- Add `x` to one less than `y`. -/
lgtm def addPred as "add-pred" (x : int) (y : int) : int :=
  x + (y - 1)

-- The command builds the `FuncDecl` field by field: the doc comment, the `as` name, the parameters
-- in order, the body, and the result type.
example : addPred =
    { docstring := "Add `x` to one less than `y`."
      name := "add-pred"
      parameters := [("x", .int), ("y", .int)]
      body := .plus (.varRef "x") (.minus (.varRef "y") (.intLit 1))
      resultType := .int } := rfl

-- And what it builds type checks, which is the point of writing it this way.
#guard addPred.check {} []

/-- Put `s` after an exclamation mark. -/
lgtm def bang (s : string) : list string :=
  ["!", s : string]

-- With no `as`, the IR name is the Lean name.
example : bang.name = "bang" := rfl
#guard bang.check {} []

lgtm def applyTo as "apply-to" (g : (int) -> int) (x : int) : int :=
  g(x)

#guard applyTo.check {} []

/-- Build a function that adds `n` to its argument. -/
lgtm def adder (n : int) : (int) -> int :=
  fun (m : int) => n + m

#guard adder.check {} []

/-- Reverse `xs` with `x` on the front. -/
lgtm def revCons as "rev-cons" (x : int) (xs : list int) : list int :=
  reverse (x :: xs)

#guard revCons.check {} []

/-- Twice one more than `n`. -/
lgtm def letDouble as "let-double" (n : int) : int :=
  let m = n + 1 in m + m

#guard letDouble.check {} []

/-- `x` when `b`, and `y` otherwise. -/
lgtm def pick (b : bool) (x : int) (y : int) : int :=
  if b then { x } else { y }

#guard pick.check {} []

-- A `bool` is a type like any other, so a declaration can return one and a list can hold them, and
-- a literal is where one comes from when no parameter has one.
lgtm def firstOf as "first-of" (b : bool) (bs : list bool) : list bool :=
  b :: bs

#guard firstOf.check {} []

/-- The two literals, which is the shortest declaration that returns a `bool`. -/
lgtm def yes : bool := true

#guard yes.check {} []
#guard !({ yes with body := [lgtm| 1] } : FuncDecl).check {} []
#guard !({ yes with resultType := [lgtm_ty| int] } : FuncDecl).check {} []

-- So a `bool` no longer has to be passed in: a conditional can be written with its condition spelled
-- out, and a list of them needs no parameter either.
lgtm def flags : list bool := [true, false, true : bool]

#guard flags.check {} []

lgtm def pickFirst as "pick-first" (x : int) (y : int) : int :=
  if true then { x } else { y }

#guard pickFirst.check {} []
#guard !({ pickFirst with body := [lgtm| if 1 then { x } else { y }] } : FuncDecl).check {} []

/-- Whether `x` and `y` are the same, which is the other way a declaration returns a `bool`. -/
lgtm def same (x : int) (y : int) : bool :=
  x == y

#guard same.check {} []

-- The operands have to share a type, the result is a `bool` and not the type compared, and a
-- function is the one thing there is no comparing: a parameter of function type cannot be an operand
-- and neither can a list of them.
#guard !({ same with body := [lgtm| x == "a"] } : FuncDecl).check {} []
#guard !({ same with resultType := [lgtm_ty| int] } : FuncDecl).check {} []

private def fnTy : Ty := [lgtm_ty| (int) -> int]

/-- `same` comparing two functions, which is the one thing a comparison cannot reach the bottom of. -/
private def sameFns : FuncDecl :=
  { same with parameters := [("g", fnTy), ("h", fnTy)], body := [lgtm| g == h] }

/-- And comparing two lists of them, which is no more comparable than its elements are. -/
private def sameFnLists : FuncDecl :=
  { sameFns with parameters := [("g", .list fnTy), ("h", .list fnTy)] }

#guard !sameFns.check {} []
#guard !sameFnLists.check {} []

-- Every other type is comparable, declared ones included, and a comparison goes where a `bool` goes.
#guard ({ same with parameters := [("x", [lgtm_ty| list string]), ("y", [lgtm_ty| list string])] }
  : FuncDecl).check {} []
#guard ({ same with parameters := [("x", [lgtm_ty| bool]), ("y", [lgtm_ty| bool])] }
  : FuncDecl).check {} []
#guard ({ pick with body := [lgtm| if x == y then { x } else { y }] } : FuncDecl).check {} []

-- A declaration with no parameters is fine, and so is one that returns a function.
lgtm def three : int := 3
#guard three.check {} []

-- `lgtm private def` makes the Lean declaration private; the `FuncDecl` it builds is the same.
/-- One more than `x`. -/
lgtm private def succ as "succ-one" (x : int) : int := x + 1
example : succ.name = "succ-one" := rfl
example : succ.docstring = "One more than `x`." := rfl
#guard succ.check {} []

-- The DSL builds ill-typed programs as readily as well-typed ones; checking is still what rejects
-- them.
#guard !({ three with body := [lgtm| 1 + "a"] } : FuncDecl).check {} []
#guard !({ revCons with body := [lgtm| reverse x] } : FuncDecl).check {} []
#guard !({ pick with body := [lgtm| if x then { x } else { y }] } : FuncDecl).check {} []
#guard !({ pick with body := [lgtm| if b then { x } else { "a" }] } : FuncDecl).check {} []

/-! ### Structs -/

-- A struct type is written with its name, which is a type like any other: it nests under `list`,
-- appears in a function type, and can be spelled with a string when it is not a Lean identifier.
example : [lgtm_ty| struct Point] = Ty.struct "Point" := rfl
example : [lgtm_ty| struct "my-struct"] = Ty.struct "my-struct" := rfl
example : [lgtm_ty| list struct Point] = Ty.list (.struct "Point") := rfl
example : [lgtm_ty| (struct Point) -> struct Point]
    = Ty.fn [.struct "Point"] (.struct "Point") := rfl

-- `new` gives each field an expression, in the order written.
example : [lgtm| new Point { x = 1, y = 2 }]
    = Expression.structNew "Point" [("x", .intLit 1), ("y", .intLit 2)] := rfl
example : [lgtm| new "my-struct" { f = n }]
    = Expression.structNew "my-struct" [("f", .varRef "n")] := rfl
example : [lgtm| new Point {}] = Expression.structNew "Point" [] := rfl
example : [lgtm| new Point { x = f(1) + 1, y = [2 : int] }]
    = Expression.structNew "Point"
        [("x", .plus (.app (.varRef "f") [.intLit 1]) (.intLit 1)),
          ("y", .lcons (.intLit 2) (.lnil .int))] := rfl

-- A field read of a bare name is a dotted identifier, which is one `structGet` per component.
example : [lgtm| p.x] = Expression.structGet (.varRef "p") "x" := rfl
example : [lgtm| p.origin.x]
    = Expression.structGet (.structGet (.varRef "p") "origin") "x" := rfl

-- A field read of anything else is the postfix `.`, and the two nest into each other.
example : [lgtm| f(1).x] = Expression.structGet (.app (.varRef "f") [.intLit 1]) "x" := rfl
example : [lgtm| f(1).origin.x]
    = Expression.structGet (.structGet (.app (.varRef "f") [.intLit 1]) "origin") "x" := rfl
example : [lgtm| (new Point { x = 1, y = 2 }).x]
    = Expression.structGet (.structNew "Point" [("x", .intLit 1), ("y", .intLit 2)]) "x" := rfl
example : [lgtm| (var "my-struct").x] = Expression.structGet (.varRef "my-struct") "x" := rfl

-- A field read is tighter than arithmetic, and a struct is an ordinary operand everywhere else.
example : [lgtm| p.x + 1] = Expression.plus (.structGet (.varRef "p") "x") (.intLit 1) := rfl
example : [lgtm| p :: ps] = Expression.lcons (.varRef "p") (.varRef "ps") := rfl
example : [lgtm| g(p.x, p.y)]
    = Expression.app (.varRef "g")
        [.structGet (.varRef "p") "x", .structGet (.varRef "p") "y"] := rfl

-- An update names only the fields it changes, in any order, and chains.
example : [lgtm| { p with x = 1 }] = Expression.structUpdate (.varRef "p") [("x", .intLit 1)] := rfl
example : [lgtm| { p with y = 2, x = 1 }]
    = Expression.structUpdate (.varRef "p") [("y", .intLit 2), ("x", .intLit 1)] := rfl
example : [lgtm| { { p with x = 1 } with y = 2 }]
    = Expression.structUpdate (.structUpdate (.varRef "p") [("x", .intLit 1)])
        [("y", .intLit 2)] := rfl
example : [lgtm| { p with x = p.x + 1 }]
    = Expression.structUpdate (.varRef "p")
        [("x", .plus (.structGet (.varRef "p") "x") (.intLit 1))] := rfl

/-- A point in the plane. -/
lgtm struct Point { x : int, y : int }

-- The command builds the `StructDecl` field by field, in the order the fields are written.
example : Point = { name := "Point", fields := [("x", .int), ("y", .int)] } := rfl

-- With no `as`, the IR name is the Lean name; `as` overrides it, as it does for `lgtm def`.
lgtm struct Renamed as "my-struct" { f : list int }
example : Renamed.name = "my-struct" := rfl
example : Renamed.fields = [("f", .list .int)] := rfl

-- A struct may have no fields, and its fields may be of any type — another struct included.
lgtm struct Nothing {}
example : Nothing.fields = [] := rfl

lgtm private struct Box { label : string, origin : struct Point, step : (int) -> int }
example : Box.fields
    = [("label", .string), ("origin", .struct "Point"), ("step", .fn [.int] .int)] := rfl

-- A field name may not be written twice: the second is one no read could reach, so the command
-- says so where the name is rather than leaving `Program.check` to turn the declaration down.
/-- error: duplicate field `x`: a declaration names each field once -/
#guard_msgs in
lgtm struct TwoXs { x : int, x : string }

-- Two structs may of course each have an `x`: a field name is scoped to the struct that declares
-- it, so the condition is on one declaration and never across them.
lgtm private struct OtherX { x : string }
example : OtherX.fields = [("x", .string)] := rfl

/-- `fun (p : Point) => new Point { x = p.y, y = p.x }` -/
lgtm def swap (p : struct Point) : struct Point :=
  new Point { x = p.y, y = p.x }

-- And what the two commands build together type checks, which is the point of writing it this way.
#guard swap.check { ss := Structs.ofDecls [Point] } []
#guard !swap.check {} []

lgtm def shift (p : struct Point) (d : int) : struct Point :=
  { p with x = p.x + d }

#guard shift.check { ss := Structs.ofDecls [Point] } []

/-- Whether two points are the same point, which is field for field. -/
lgtm def samePoint as "same-point" (p : struct Point) (q : struct Point) : bool :=
  p == q

#guard samePoint.check { ss := Structs.ofDecls [Point] } []
#guard !samePoint.check {} []

/-- The same comparison on `Box`es, which carry a `step` of function type. -/
private def sameBox : FuncDecl :=
  { samePoint with parameters := [("p", .struct "Box"), ("q", .struct "Box")] }

-- A struct is comparable when everything it carries is, so a `Box` is not — however ordinary its
-- other two fields are, and although every struct form other than `==` still works on one.
#guard !sameBox.check { ss := Structs.ofDecls [Point, Box] } []

/-! ### Inductive types -/

-- An inductive type is written with its name, and is a type like any other.
example : [lgtm_ty| inductive Color] = Ty.ind "Color" := rfl
example : [lgtm_ty| inductive "my-type"] = Ty.ind "my-type" := rfl
example : [lgtm_ty| list inductive Color] = Ty.list (.ind "Color") := rfl
example : [lgtm_ty| (inductive Color) -> struct Point]
    = Ty.fn [.ind "Color"] (.struct "Point") := rfl

-- `new Type.Ctor(...)` applies a constructor, with the parentheses written even when it takes
-- nothing, the way a call of no arguments is.
example : [lgtm| new Color.Red()] = Expression.indNew "Color" "Red" [] := rfl
example : [lgtm| new Color.Rgb(1, 2, 3)]
    = Expression.indNew "Color" "Rgb" [.intLit 1, .intLit 2, .intLit 3] := rfl
example : [lgtm| new Shape.Rect(w + 1, f(2))]
    = Expression.indNew "Shape" "Rect"
        [.plus (.varRef "w") (.intLit 1), .app (.varRef "f") [.intLit 2]] := rfl
example : [lgtm| new "my-type" "my-ctor"(n)]
    = Expression.indNew "my-type" "my-ctor" [.varRef "n"] := rfl

-- And it is an ordinary operand everywhere else, constructors nested inside it included.
example : [lgtm| new Color.Red() :: cs]
    = Expression.lcons (.indNew "Color" "Red" []) (.varRef "cs") := rfl
example : [lgtm| new Tree.Node(new Tree.Leaf(), new Tree.Leaf())]
    = Expression.indNew "Tree" "Node" [.indNew "Tree" "Leaf" [], .indNew "Tree" "Leaf" []] := rfl

-- A `match` is one alternative per constructor, each binding a name to everything that constructor
-- carries.
example : [lgtm| match c with | Red => 0 | Rgb(r, g, b) => r]
    = Expression.indMatch (.varRef "c")
        [("Red", [], .intLit 0), ("Rgb", ["r", "g", "b"], .varRef "r")] := rfl
example : [lgtm| match f(1) with | Circle(r) => r]
    = Expression.indMatch (.app (.varRef "f") [.intLit 1]) [("Circle", ["r"], .varRef "r")] := rfl

-- An alternative's expression extends as far right as it can, so it stops only at the next `|`, and
-- a `match` inside one needs parentheses just as a `let` does.
example : [lgtm| match c with | Red => 1 + 2 | Green => let x = 1 in x + x]
    = Expression.indMatch (.varRef "c")
        [("Red", [], .plus (.intLit 1) (.intLit 2)),
          ("Green", [], .let_ "x" (.intLit 1) (.plus (.varRef "x") (.varRef "x")))] := rfl
example : [lgtm| (match c with | Red => 1) + 2]
    = Expression.plus (.indMatch (.varRef "c") [("Red", [], .intLit 1)]) (.intLit 2) := rfl

-- The parser is not the exhaustiveness check: a match with no alternatives at all is written the
-- same way as any other, and it is the type checker that has nothing to say for it.
example : [lgtm| match c with] = Expression.indMatch (.varRef "c") [] := rfl

/-- A colour. -/
lgtm inductive Color { Red, Green, Blue }

-- The command builds the `InductiveDecl` constructor by constructor, in the order they are written,
-- with an empty list of data types for the ones that carry nothing.
example : Color = { name := "Color", constructors := [("Red", []), ("Green", []), ("Blue", [])] } :=
  rfl

lgtm inductive Shape { Circle(int), Rect(int, int) }
example : Shape.constructors = [("Circle", [.int]), ("Rect", [.int, .int])] := rfl

-- A constructor's data may be of any type, another inductive type and the type being declared
-- included: nothing about a constructor's types is resolved when it is declared.
lgtm inductive Tree { Leaf, Node(inductive Tree, inductive Tree) }
example : Tree.constructors = [("Leaf", []), ("Node", [.ind "Tree", .ind "Tree"])] := rfl

lgtm inductive Wrapped { C(list int, struct Point, (int) -> int) }
example : Wrapped.constructors
    = [("C", [.list .int, .struct "Point", .fn [.int] .int])] := rfl

-- With no `as`, the IR name is the Lean name; `as` overrides it, and a type may declare no
-- constructors at all — nothing can build a value of it, and nothing can take one apart.
lgtm inductive RenamedInd as "my-type" { C }
example : RenamedInd.name = "my-type" := rfl

lgtm private inductive NoCtors {}
example : NoCtors.constructors = [] := rfl

-- A constructor name may not be written twice, for the reason a field name may not: the second is
-- one nothing could build and no alternative of a match could be checked against.
/-- error: duplicate constructor `Red`: a declaration names each constructor once -/
#guard_msgs in
lgtm inductive TwoReds { Red, Green, Red(int) }

-- Two types may each have a `Red` all the same: a constructor name is scoped to the type that
-- declares it, which is why `new` and `Value.ind` both name the type as well.
lgtm private inductive Hue { Red, Green }
example : Hue.constructors = [("Red", []), ("Green", [])] := rfl

/-- The perimeter of `s`, which is what a `match` is for: one answer per constructor, computed from
what that constructor carries. -/
lgtm def perimeter (s : inductive Shape) : int :=
  match s with | Circle(r) => r + r + r + r + r + r | Rect(w, h) => w + w + h + h

-- And what the two commands build together type checks, which is the point of writing it this way.
#guard perimeter.check { is := Inductives.ofDecls [Shape] } []
#guard !perimeter.check {} []

/-- `Rect` with both sides `n`, which is the other half: a constructor applied to values. -/
lgtm def square (n : int) : inductive Shape :=
  new Shape.Rect(n, n)

#guard square.check { is := Inductives.ofDecls [Shape] } []

/-- Whether two trees are the same tree: the same constructors all the way down, carrying the same
data.  A type being recursive is no obstacle to comparing two values of it — each value is finite —
which is what makes this check. -/
lgtm def sameTree as "same-tree" (a : inductive Tree) (b : inductive Tree) : bool :=
  a == b

#guard sameTree.check { is := Inductives.ofDecls [Tree] } []
#guard !sameTree.check {} []

/-- The same comparison on `Wrapped`, whose one constructor carries a function among its data. -/
private def sameWrapped : FuncDecl :=
  { sameTree with parameters := [("a", .ind "Wrapped"), ("b", .ind "Wrapped")] }

#guard !sameWrapped.check { ss := Structs.ofDecls [Point], is := Inductives.ofDecls [Wrapped] } []

/-! ### Options -/

-- An option type holds another type, which it carries rather than names, so it nests both ways and
-- needs no declaration to be written.
example : [lgtm_ty| option int] = Ty.option .int := rfl
example : [lgtm_ty| option option int] = Ty.option (.option .int) := rfl
example : [lgtm_ty| option list int] = Ty.option (.list .int) := rfl
example : [lgtm_ty| list option int] = Ty.list (.option .int) := rfl
example : [lgtm_ty| option struct Point] = Ty.option (.struct "Point") := rfl
example : [lgtm_ty| option ((int) -> int)] = Ty.option (.fn [.int] .int) := rfl
example : [lgtm_ty| (option int) -> option string]
    = Ty.fn [.option .int] (.option .string) := rfl

-- The option holding a value takes no annotation, and the empty one takes the type it is empty at.
example : [lgtm| some(1)] = Expression.optionSome (.intLit 1) := rfl
example : [lgtm| some(x + 1)] = Expression.optionSome (.plus (.varRef "x") (.intLit 1)) := rfl
example : [lgtm| some(some(1))] = Expression.optionSome (.optionSome (.intLit 1)) := rfl
example : [lgtm| none : int] = Expression.optionNone .int := rfl
example : [lgtm| none : list string] = Expression.optionNone (.list .string) := rfl
example : [lgtm| none : option int] = Expression.optionNone (.option .int) := rfl
example : [lgtm| none : ((int) -> int)] = Expression.optionNone (.fn [.int] .int) := rfl
example : [lgtm| some(none : int)] = Expression.optionSome (.optionNone .int) := rfl

-- `some` and `none` are keywords, so neither is a variable name inside a DSL term; outside one they
-- are Lean's own, which declaring them with `&` is what preserves.
example : [lgtm| var "some"] = Expression.varRef "some" := rfl
example : [lgtm| var "none"] = Expression.varRef "none" := rfl
example : (some 1 : Option Nat) = Option.some 1 := rfl
example : (none : Option Nat) = Option.none := rfl

-- Both are ordinary operands: the annotation stops at the type, so a `+` or a `==` after one
-- applies to the whole of it, and neither form needs parentheses to be an argument.
example : [lgtm| some(1) == none : int]
    = Expression.equals (.optionSome (.intLit 1)) (.optionNone .int) := rfl
example : [lgtm| f(some(1), none : int)]
    = Expression.app (.varRef "f") [.optionSome (.intLit 1), .optionNone .int] := rfl
example : [lgtm| some(1) :: os] = Expression.lcons (.optionSome (.intLit 1)) (.varRef "os") := rfl
example : [lgtm| let o = some(1) in o]
    = Expression.let_ "o" (.optionSome (.intLit 1)) (.varRef "o") := rfl
example : [lgtm| if b then { some(1) } else { none : int }]
    = Expression.ite (.varRef "b") (.optionSome (.intLit 1)) (.optionNone .int) := rfl
example : [lgtm| fun (o : option int) => o]
    = Expression.lam [("o", .option .int)] (.varRef "o") := rfl

-- A list literal ends with an annotation of its own, so an empty option inside one is parenthesized
-- to say which `:` is which.
example : [lgtm| [(none : int) : option int]]
    = Expression.lcons (.optionNone .int) (.lnil (.option .int)) := rfl
example : [lgtm| [some(1), (none : int) : option int]]
    = Expression.lcons (.optionSome (.intLit 1))
        (.lcons (.optionNone .int) (.lnil (.option .int))) := rfl

-- A `match` on an option is the two cases it has, which is an `optionMatch` rather than an
-- `indMatch`: the empty case computes with nothing and the other binds what the option held.
example : [lgtm| match o with | none => 0 | some(x) => x + 1]
    = Expression.optionMatch (.varRef "o") (.intLit 0) "x"
        (.plus (.varRef "x") (.intLit 1)) := rfl
example : [lgtm| match f(1) with | none => "" | some(s) => s]
    = Expression.optionMatch (.app (.varRef "f") [.intLit 1]) (.stringLit "") "s"
        (.varRef "s") := rfl
example : [lgtm| match some(1) with | none => 0 | some(x) => x]
    = Expression.optionMatch (.optionSome (.intLit 1)) (.intLit 0) "x" (.varRef "x") := rfl

-- An alternative's expression extends as far right as it can here too, so a match nested in one
-- needs no parentheses and one nested in the scrutinee does.
example : [lgtm| match o with | none => 0 | some(x) => match x with | none => 1 | some(y) => y]
    = Expression.optionMatch (.varRef "o") (.intLit 0) "x"
        (.optionMatch (.varRef "x") (.intLit 1) "y" (.varRef "y")) := rfl
example : [lgtm| (match o with | none => 0 | some(x) => x) + 1]
    = Expression.plus (.optionMatch (.varRef "o") (.intLit 0) "x" (.varRef "x")) (.intLit 1) := rfl

-- A match naming neither is the `indMatch` it was, which is what the special case is special to.
example : [lgtm| match c with | Red => 0 | Rgb(r, g, b) => r]
    = Expression.indMatch (.varRef "c")
        [("Red", [], .intLit 0), ("Rgb", ["r", "g", "b"], .varRef "r")] := rfl

/-- One more than what `o` holds, and zero when it holds nothing: the two option forms and the match
between them, which is what a declaration returning an `int` from an option looks like. -/
lgtm def succOrZero as "succ-or-zero" (o : option int) : int :=
  match o with | none => 0 | some(x) => x + 1

-- An option needs no declaration to be well formed, so this checks against no `TypeDecls` at all.
#guard succOrZero.check {} []

-- The two cases have to share a type, and the name bound is the type the option holds — so `x + 1`
-- is an `int` because the parameter is an `option int`.
#guard !({ succOrZero with
  body := [lgtm| match o with | none => 0 | some(x) => "a"] } : FuncDecl).check {} []
#guard !({ succOrZero with
  parameters := [("o", [lgtm_ty| option string])] } : FuncDecl).check {} []

-- And the scrutinee has to be an option: a list is not one, however much the match looks like it
-- could take one apart.
#guard !({ succOrZero with
  parameters := [("o", [lgtm_ty| list int])] } : FuncDecl).check {} []

/-- `n`, held in an option, which is the other half: a value put into one rather than taken out. -/
lgtm def justInt as "just-int" (n : int) : option int :=
  some(n)

#guard justInt.check {} []
#guard !({ justInt with resultType := [lgtm_ty| option string] } : FuncDecl).check {} []

/-- Nothing, at `int`: the shortest declaration returning an option, and the one place the
annotation is all there is to go on. -/
lgtm def noInt as "no-int" : option int :=
  none : int

#guard noInt.check {} []
#guard !({ noInt with resultType := [lgtm_ty| option string] } : FuncDecl).check {} []

/-- Whether two options are the same option, which an option is as comparable as what it holds. -/
lgtm def sameOpt as "same-opt" (a : option int) (b : option int) : bool :=
  a == b

#guard sameOpt.check {} []

-- So an option of function type is no more comparable than the functions it holds.
#guard !({ sameOpt with
  parameters := [("a", .option fnTy), ("b", .option fnTy)] } : FuncDecl).check {} []

-- Both alternatives are required and in the order `optionMatch` holds them, since there is nothing
-- else a `match` naming `none` could have meant.
/-- error: a match on an option takes `none` first and `some` second -/
#guard_msgs(error) in
#check [lgtm| match o with | some(x) => x | none => 0]

/-- error: a match on an option has two alternatives: `| none => ... | some(x) => ...` -/
#guard_msgs(error) in
#check [lgtm| match o with | none => 0]

/-- error: `some` holds one value, so its alternative binds one name: `| some(x) => ...` -/
#guard_msgs(error) in
#check [lgtm| match o with | none => 0 | some(x, y) => x]

/-- error: `none` holds nothing, so its alternative binds no names -/
#guard_msgs(error) in
#check [lgtm| match o with | none(x) => 0 | some(y) => y]
