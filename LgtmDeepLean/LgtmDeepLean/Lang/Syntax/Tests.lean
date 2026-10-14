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

-- `&&` and `||` are looser than `==`, which is what lets a comparison be an operand of either
-- without parentheses, and `||` is the looser of the two.
example : [lgtm| b && c] = Expression.boolAnd (.varRef "b") (.varRef "c") := rfl
example : [lgtm| b || c] = Expression.boolOr (.varRef "b") (.varRef "c") := rfl
example : [lgtm| x == y && b]
    = Expression.boolAnd (.equals (.varRef "x") (.varRef "y")) (.varRef "b") := rfl
example : [lgtm| b && x == y]
    = Expression.boolAnd (.varRef "b") (.equals (.varRef "x") (.varRef "y")) := rfl
example : [lgtm| length xs == 0 || b]
    = Expression.boolOr (.equals (.listLength (.varRef "xs")) (.intLit 0)) (.varRef "b") := rfl
example : [lgtm| a || b && c]
    = Expression.boolOr (.varRef "a") (.boolAnd (.varRef "b") (.varRef "c")) := rfl
example : [lgtm| a && b || c]
    = Expression.boolOr (.boolAnd (.varRef "a") (.varRef "b")) (.varRef "c") := rfl
example : [lgtm| (a || b) && c]
    = Expression.boolAnd (.boolOr (.varRef "a") (.varRef "b")) (.varRef "c") := rfl

-- Both are left-associative, unlike `==`, which takes parentheses to chain at all.
example : [lgtm| a && b && c]
    = Expression.boolAnd (.boolAnd (.varRef "a") (.varRef "b")) (.varRef "c") := rfl
example : [lgtm| a || b || c]
    = Expression.boolOr (.boolOr (.varRef "a") (.varRef "b")) (.varRef "c") := rfl
example : [lgtm| a && (b && c)]
    = Expression.boolAnd (.varRef "a") (.boolAnd (.varRef "b") (.varRef "c")) := rfl

-- What they produce is a `bool` like any other, so every form that reads one reads these: a
-- condition, an operand of another one, a call's argument, a list of them.
example : [lgtm| if b && c then { 1 } else { 2 }]
    = Expression.ite (.boolAnd (.varRef "b") (.varRef "c")) (.intLit 1) (.intLit 2) := rfl
example : [lgtm| f(b || c)]
    = Expression.app (.varRef "f") [.boolOr (.varRef "b") (.varRef "c")] := rfl
example : [lgtm| fun (b : bool) => b && true]
    = Expression.lam [("b", .bool)] (.boolAnd (.varRef "b") (.boolLit true)) := rfl
example : [lgtm| let e = b || c in e]
    = Expression.let_ "e" (.boolOr (.varRef "b") (.varRef "c")) (.varRef "e") := rfl
example : [lgtm| [b && c, true : bool]]
    = Expression.lcons (.boolAnd (.varRef "b") (.varRef "c"))
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

-- `length` is written like `reverse`, and binds as tightly, so it takes one operand and no more.
example : [lgtm| length xs] = Expression.listLength (.varRef "xs") := rfl
example : [lgtm| length (x :: xs)]
    = Expression.listLength (.lcons (.varRef "x") (.varRef "xs")) := rfl
example : [lgtm| length [1, 2 : int]]
    = Expression.listLength (.lcons (.intLit 1) (.lcons (.intLit 2) (.lnil .int))) := rfl
example : [lgtm| length reverse xs]
    = Expression.listLength (.listReverse (.varRef "xs")) := rfl

-- Binding tighter than `+` and `==` is what makes an `int` out of a length usable in place.
example : [lgtm| length xs + 1]
    = Expression.plus (.listLength (.varRef "xs")) (.intLit 1) := rfl
example : [lgtm| length xs == length ys]
    = Expression.equals (.listLength (.varRef "xs")) (.listLength (.varRef "ys")) := rfl

-- A variable of a keyword's name takes the escape hatch, the way `reverse` and `toList` do.
example : [lgtm| var "length"] = Expression.varRef "length" := rfl

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

/-- Every element of `xs` with one added to it.  The function takes one parameter, at the list's
element type, which is what the `list` tag on the `map` is standing in for. -/
lgtm def bumpAll as "bump-all" (xs : list int) : list int :=
  map list xs (fun (x : int) => x + 1)

#guard bumpAll.check {} []

-- The element type is the one thing a mapping over a list does not carry through, so what the
-- function returns is what the result is a list of and the declaration has to say so.
#guard ({ bumpAll with
  body := [lgtm| map list xs (fun (x : int) => "a")]
  resultType := [lgtm_ty| list string] } : FuncDecl).check {} []
#guard !({ bumpAll with body := [lgtm| map list xs (fun (x : int) => "a")] } : FuncDecl).check {} []

-- The function is held to the element type, and to taking one parameter: a hashmap's two-parameter
-- function is what the other tag is for, and no `list` mapping accepts one.
#guard !({ bumpAll with body := [lgtm| map list xs (fun (x : string) => 1)] } : FuncDecl).check {} []
#guard !({ bumpAll with body := [lgtm| map list xs (fun (x : int) (y : int) => 1)] }
  : FuncDecl).check {} []

-- And the tag decides nothing about the types: a `list` mapping over a hashmap is ill typed, as a
-- `hashmap` mapping over a list is.
#guard !({ bumpAll with body := [lgtm| map list hashmap(string, int) (fun (x : int) => 1)] }
  : FuncDecl).check {} []
#guard !({ bumpAll with body := [lgtm| map hashmap xs (fun (x : int) (y : int) => 1)] }
  : FuncDecl).check {} []

/-- Whether `xs` is empty or is `ys`: the shortest declaration the two boolean operators are in,
and the one place their being looser than `==` is what keeps a comparison on either side
unparenthesized. -/
lgtm def emptyOrEqual as "empty-or-equal" (xs : list int) (ys : list int) : bool :=
  length xs == 0 || xs == ys

#guard emptyOrEqual.check {} []
#guard ({ emptyOrEqual with body := [lgtm| length xs == 0 && xs == ys] } : FuncDecl).check {} []

-- Both operands have to be `bool`s, and what comes out is one whatever they were about: there is no
-- truthiness to read an `int` as, the same way a conditional's condition has none.
#guard !({ emptyOrEqual with body := [lgtm| length xs || xs == ys] } : FuncDecl).check {} []
#guard !({ emptyOrEqual with body := [lgtm| xs == ys && length xs] } : FuncDecl).check {} []
#guard !({ emptyOrEqual with resultType := [lgtm_ty| int] } : FuncDecl).check {} []

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

-- A declaration is called by its IR name, and a dotted one is the whole name rather than a field
-- read: `Nested.one` is the declaration below, which is how one declaration calls another.  A
-- nullary one still takes the parentheses — `Ty.fn [] .int` is not `Ty.int`.
lgtm def Nested.one : int := 1
example : [lgtm| Nested.one] = Expression.varRef "Nested.one" := rfl
example : [lgtm| Nested.one()] = Expression.app (.varRef "Nested.one") [] := rfl
#guard ({ three with body := [lgtm| Nested.one()] } : FuncDecl).check {} [("Nested.one", Nested.one)]
#guard !({ three with body := [lgtm| Nested.one] } : FuncDecl).check {} [("Nested.one", Nested.one)]

-- A dotted name no declaration has taken is a variable and one field read per component, and the
-- postfix `.` is what reads a field off a name that is taken.
example : [lgtm| Nested.two] = Expression.structGet (.varRef "Nested") "two" := rfl
example : [lgtm| (var "Nested.one").x] = Expression.structGet (.varRef "Nested.one") "x" := rfl

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

/-! ### Hashmaps -/

-- A hashmap type is written with the two types it relates, in that order, and is a type like any
-- other: it nests both ways and needs no declaration to be written.
example : [lgtm_ty| hashmap string int] = Ty.hashmap .string .int := rfl
example : [lgtm_ty| hashmap int string] = Ty.hashmap .int .string := rfl
example : [lgtm_ty| hashmap string list int] = Ty.hashmap .string (.list .int) := rfl
example : [lgtm_ty| hashmap list string int] = Ty.hashmap (.list .string) .int := rfl
example : [lgtm_ty| hashmap string option int] = Ty.hashmap .string (.option .int) := rfl
example : [lgtm_ty| hashmap string struct Point] = Ty.hashmap .string (.struct "Point") := rfl
example : [lgtm_ty| hashmap string ((int) -> int)] = Ty.hashmap .string (.fn [.int] .int) := rfl
example : [lgtm_ty| hashmap string hashmap string int]
    = Ty.hashmap .string (.hashmap .string .int) := rfl
example : [lgtm_ty| list hashmap string int] = Ty.list (.hashmap .string .int) := rfl
example : [lgtm_ty| option hashmap string int] = Ty.option (.hashmap .string .int) := rfl
example : [lgtm_ty| (hashmap string int) -> int] = Ty.fn [.hashmap .string .int] .int := rfl

-- The empty map carries both of its types, for the reason an empty list carries its one: it binds
-- nothing, so there is neither a key nor a value to read either off.
example : [lgtm| hashmap(string, int)] = Expression.hashmapEmpty .string .int := rfl
example : [lgtm| hashmap(int, list string)] = Expression.hashmapEmpty .int (.list .string) := rfl
example : [lgtm| hashmap(string, hashmap string int)]
    = Expression.hashmapEmpty .string (.hashmap .string .int) := rfl
example : [lgtm| hashmap(string, (int) -> int)]
    = Expression.hashmapEmpty .string (.fn [.int] .int) := rfl

-- `hashmap` is a keyword, so it is no variable name inside a DSL term; outside one it is an
-- ordinary Lean identifier, which declaring it with `&` is what preserves.
example : [lgtm| var "hashmap"] = Expression.varRef "hashmap" := rfl

-- A lookup is written with no space before the `[`, which is what tells it from a list literal.
example : [lgtm| m[k]] = Expression.hashmapGet (.varRef "m") (.varRef "k") := rfl
example : [lgtm| m["a"]] = Expression.hashmapGet (.varRef "m") (.stringLit "a") := rfl
example : [lgtm| m[x + 1]]
    = Expression.hashmapGet (.varRef "m") (.plus (.varRef "x") (.intLit 1)) := rfl

-- It binds as tightly as a field read does, and nests into itself and into the other postfix forms.
example : [lgtm| m[a][b]]
    = Expression.hashmapGet (.hashmapGet (.varRef "m") (.varRef "a")) (.varRef "b") := rfl
example : [lgtm| p.m[k]] = Expression.hashmapGet (.structGet (.varRef "p") "m") (.varRef "k") := rfl
example : [lgtm| f(1)[k]]
    = Expression.hashmapGet (.app (.varRef "f") [.intLit 1]) (.varRef "k") := rfl

-- And what it produces is an ordinary operand: an option, so a comparison and a match both read one
-- with no parentheses.
example : [lgtm| m[k] + 1]
    = Expression.plus (.hashmapGet (.varRef "m") (.varRef "k")) (.intLit 1) := rfl
example : [lgtm| m[k] == none : int]
    = Expression.equals (.hashmapGet (.varRef "m") (.varRef "k")) (.optionNone .int) := rfl
example : [lgtm| match m[k] with | none => 0 | some(x) => x]
    = Expression.optionMatch (.hashmapGet (.varRef "m") (.varRef "k")) (.intLit 0) "x"
        (.varRef "x") := rfl

-- An update names its keys in brackets and is one `hashmapPut` apiece, applied left to right, so
-- writing two is the same as nesting two.
example : [lgtm| { m with [k] = 1 }]
    = Expression.hashmapPut (.varRef "m") (.varRef "k") (.intLit 1) := rfl
example : [lgtm| { m with ["a"] = 1, ["b"] = 2 }]
    = Expression.hashmapPut (.hashmapPut (.varRef "m") (.stringLit "a") (.intLit 1))
        (.stringLit "b") (.intLit 2) := rfl
example : [lgtm| { { m with ["a"] = 1 } with ["b"] = 2 }]
    = Expression.hashmapPut (.hashmapPut (.varRef "m") (.stringLit "a") (.intLit 1))
        (.stringLit "b") (.intLit 2) := rfl
example : [lgtm| { hashmap(string, int) with ["a"] = 1 }]
    = Expression.hashmapPut (.hashmapEmpty .string .int) (.stringLit "a") (.intLit 1) := rfl
example : [lgtm| { m with [k] = x + 1 }]
    = Expression.hashmapPut (.varRef "m") (.varRef "k")
        (.plus (.varRef "x") (.intLit 1)) := rfl

-- The brackets are the whole of what tells a map update from a struct update — a field is a name
-- and a key is an expression — so the two forms never meet and `{ p with }` is the struct update it
-- has always been.
example : [lgtm| { p with x = 1 }] = Expression.structUpdate (.varRef "p") [("x", .intLit 1)] := rfl
example : [lgtm| { p with }] = Expression.structUpdate (.varRef "p") [] := rfl

-- An update is an operand like any other, so a lookup reads one with no parentheses.
example : [lgtm| { m with ["a"] = 1 }["a"]]
    = Expression.hashmapGet (.hashmapPut (.varRef "m") (.stringLit "a") (.intLit 1))
        (.stringLit "a") := rfl

-- A tuple type lists its types in one group in parentheses, the way a function type's parameters
-- are listed and unlike `hashmap`'s two: the group is what says how many there are, so a function
-- type among them needs no parentheses of its own and there is an empty one to write.
example : [lgtm_ty| tuple(string, int)] = Ty.tuple [.string, .int] := rfl
example : [lgtm_ty| tuple(int, string)] = Ty.tuple [.int, .string] := rfl
example : [lgtm_ty| tuple()] = Ty.tuple [] := rfl
example : [lgtm_ty| tuple(int)] = Ty.tuple [.int] := rfl
example : [lgtm_ty| tuple(int, string, bool)] = Ty.tuple [.int, .string, .bool] := rfl
example : [lgtm_ty| tuple(list int, option string)]
    = Ty.tuple [.list .int, .option .string] := rfl
example : [lgtm_ty| tuple(string, (int) -> int)] = Ty.tuple [.string, .fn [.int] .int] := rfl
example : [lgtm_ty| tuple(string, tuple(int, bool))]
    = Ty.tuple [.string, .tuple [.int, .bool]] := rfl
example : [lgtm_ty| list tuple(string, int)] = Ty.list (.tuple [.string, .int]) := rfl
example : [lgtm_ty| hashmap tuple(string, int) int]
    = Ty.hashmap (.tuple [.string, .int]) .int := rfl

-- A conversion is a prefix keyword binding as tightly as `reverse`, so it reads a lookup's operand
-- and takes parentheses to reach further.
example : [lgtm| toList m] = Expression.hashmapToList (.varRef "m") := rfl
example : [lgtm| toList p.m] = Expression.hashmapToList (.structGet (.varRef "p") "m") := rfl
example : [lgtm| toList f(1)] = Expression.hashmapToList (.app (.varRef "f") [.intLit 1]) := rfl
example : [lgtm| toList hashmap(string, int)]
    = Expression.hashmapToList (.hashmapEmpty .string .int) := rfl
example : [lgtm| toList ({ m with [k] = 1 })]
    = Expression.hashmapToList (.hashmapPut (.varRef "m") (.varRef "k") (.intLit 1)) := rfl

-- And what it produces is an ordinary list operand: `reverse` reads one, a cons extends one, and a
-- comparison against the empty list is what asking whether a map binds anything comes to.
example : [lgtm| reverse toList m]
    = Expression.listReverse (.hashmapToList (.varRef "m")) := rfl
example : [lgtm| toList m == [: tuple(string, int)]]
    = Expression.equals (.hashmapToList (.varRef "m")) (.lnil (.tuple [.string, .int])) := rfl

-- `toList` is a keyword, so it is no variable name inside a DSL term; outside one it is an ordinary
-- Lean identifier, which declaring it with `&` is what preserves.
example : [lgtm| var "toList"] = Expression.varRef "toList" := rfl

-- A mapping is a prefix keyword with a tag and two operands, both of them binding as tightly as
-- `toList`'s one, so a name, a field read and a call are each read whole on either side.
example : [lgtm| map hashmap m f] = Expression.hashmapMap (.varRef "m") (.varRef "f") := rfl
example : [lgtm| map hashmap p.m f]
    = Expression.hashmapMap (.structGet (.varRef "p") "m") (.varRef "f") := rfl
example : [lgtm| map hashmap m g(1)]
    = Expression.hashmapMap (.varRef "m") (.app (.varRef "g") [.intLit 1]) := rfl
example : [lgtm| map hashmap hashmap(string, int) f]
    = Expression.hashmapMap (.hashmapEmpty .string .int) (.varRef "f") := rfl

-- A function written out is the loosest form there is, so it takes the parentheses an operand at
-- that level needs — and the key comes before the value, which is the order the parameters go in.
example : [lgtm| map hashmap m (fun (k : string) (v : int) => v + 1)]
    = Expression.hashmapMap (.varRef "m")
        (.lam [("k", .string), ("v", .int)] (.plus (.varRef "v") (.intLit 1))) := rfl
example : [lgtm| map hashmap m (fun (k : string) (v : int) => k)]
    = Expression.hashmapMap (.varRef "m") (.lam [("k", .string), ("v", .int)] (.varRef "k")) := rfl

-- What it produces is a map, so every form that reads one reads this: a lookup, an update, another
-- mapping, and a conversion.
example : [lgtm| (map hashmap m f)[k]]
    = Expression.hashmapGet (.hashmapMap (.varRef "m") (.varRef "f")) (.varRef "k") := rfl
example : [lgtm| { map hashmap m f with [k] = 1 }]
    = Expression.hashmapPut (.hashmapMap (.varRef "m") (.varRef "f")) (.varRef "k")
        (.intLit 1) := rfl
example : [lgtm| map hashmap (map hashmap m f) g]
    = Expression.hashmapMap (.hashmapMap (.varRef "m") (.varRef "f")) (.varRef "g") := rfl
example : [lgtm| toList (map hashmap m f)]
    = Expression.hashmapToList (.hashmapMap (.varRef "m") (.varRef "f")) := rfl

-- The `list` tag is the same keyword over the other thing there is to map over, and it reads its two
-- operands the same way.
example : [lgtm| map list xs f] = Expression.listMap (.varRef "xs") (.varRef "f") := rfl
example : [lgtm| map list p.items f]
    = Expression.listMap (.structGet (.varRef "p") "items") (.varRef "f") := rfl
example : [lgtm| map list g(1) f]
    = Expression.listMap (.app (.varRef "g") [.intLit 1]) (.varRef "f") := rfl
example : [lgtm| map list [1, 2 : int] f]
    = Expression.listMap (.lcons (.intLit 1) (.lcons (.intLit 2) (.lnil .int))) (.varRef "f") := rfl
example : [lgtm| map list [: int] f] = Expression.listMap (.lnil .int) (.varRef "f") := rfl

-- Its function takes one parameter where a hashmap's takes two, which is what the tag is standing in
-- for: an element is one value where a binding is a key beside its value.
example : [lgtm| map list xs (fun (x : int) => x + 1)]
    = Expression.listMap (.varRef "xs") (.lam [("x", .int)] (.plus (.varRef "x") (.intLit 1)))
    := rfl

-- What it produces is a list, so every form that reads one reads this: a reversal, a length, a cons,
-- and another mapping.
example : [lgtm| reverse (map list xs f)]
    = Expression.listReverse (.listMap (.varRef "xs") (.varRef "f")) := rfl
example : [lgtm| length (map list xs f)]
    = Expression.listLength (.listMap (.varRef "xs") (.varRef "f")) := rfl
example : [lgtm| x :: map list xs f]
    = Expression.lcons (.varRef "x") (.listMap (.varRef "xs") (.varRef "f")) := rfl
example : [lgtm| map list (map list xs f) g]
    = Expression.listMap (.listMap (.varRef "xs") (.varRef "f")) (.varRef "g") := rfl

-- The two tags are what tell the forms apart, and nothing else about a `map` does: the same operands
-- under the other tag are the other expression.
example : [lgtm| map list m f] = Expression.listMap (.varRef "m") (.varRef "f") := rfl
example : [lgtm| map hashmap xs f] = Expression.hashmapMap (.varRef "xs") (.varRef "f") := rfl

-- A conversion produces a list of tuples, which is a list like any other, so the two forms compose
-- the way the IR's types say they do rather than the way the keyword might suggest.
example : [lgtm| map list (toList m) f]
    = Expression.listMap (.hashmapToList (.varRef "m")) (.varRef "f") := rfl

-- `map` is a keyword, so it is no variable name inside a DSL term; outside one it is an ordinary
-- Lean identifier, which declaring it with `&` is what preserves.  `list` is one too, now that it
-- tags a mapping, and takes the same escape hatch.
example : [lgtm| var "map"] = Expression.varRef "map" := rfl
example : [lgtm| var "list"] = Expression.varRef "list" := rfl

/-- The empty map from `string` to `int`: the shortest declaration that returns one, and the one
place the annotations are all there is to go on. -/
lgtm def noneBound as "none-bound" : hashmap string int :=
  hashmap(string, int)

-- A hashmap needs no declaration to be well formed, so this checks against no `TypeDecls` at all.
#guard noneBound.check {} []
#guard !({ noneBound with resultType := [lgtm_ty| hashmap int string] } : FuncDecl).check {} []

/-- `m` with `k` bound to `v`, which is the other half: a binding put into a map rather than read
out of one. -/
lgtm def bind (m : hashmap string int) (k : string) (v : int) : hashmap string int :=
  { m with [k] = v }

#guard bind.check {} []
#guard !({ bind with body := [lgtm| { m with [v] = k }] } : FuncDecl).check {} []
#guard !({ bind with resultType := [lgtm_ty| hashmap string string] } : FuncDecl).check {} []

/-- What `k` is bound to in `m`, and zero when it is bound to nothing: the two halves of a lookup,
which is what an option result is for. -/
lgtm def getOr as "get-or" (m : hashmap string int) (k : string) : int :=
  match m[k] with | none => 0 | some(x) => x

#guard getOr.check {} []
#guard !({ getOr with resultType := [lgtm_ty| option int] } : FuncDecl).check {} []
#guard !({ getOr with parameters := [("m", [lgtm_ty| hashmap string string]), ("k", .string)] }
  : FuncDecl).check {} []

/-- Every value of `m` with one added to it, the keys left as they were.  The function takes the key
as well as the value, so its parameters are the map's two types in that order. -/
lgtm def bump (m : hashmap string int) : hashmap string int :=
  map hashmap m (fun (k : string) (v : int) => v + 1)

#guard bump.check {} []
#guard !({ bump with body := [lgtm| map hashmap m (fun (v : int) (k : string) => v + 1)] }
  : FuncDecl).check {} []
#guard !({ bump with resultType := [lgtm_ty| hashmap string string] } : FuncDecl).check {} []

-- A mapping is what makes the value type the one thing about a map that can change, since the keys
-- it hands back are the ones it was given: a map to `string` comes out of a map to `int` and the
-- declaration says so.
#guard ({ bump with
  body := [lgtm| map hashmap m (fun (k : string) (v : int) => k)]
  resultType := [lgtm_ty| hashmap string string] } : FuncDecl).check {} []

-- The key type has to be one a comparison can reach the bottom of, which is the one condition every
-- one of the forms shares and the one way an annotation alone makes a map ill typed.
#guard !({ noneBound with
  body := [lgtm| hashmap((int) -> int, int)]
  resultType := [lgtm_ty| hashmap ((int) -> int) int] } : FuncDecl).check {} []

-- The *value* type is under no such condition: nothing compares a value a map holds.
#guard ({ noneBound with
  body := [lgtm| hashmap(string, (int) -> int)]
  resultType := [lgtm_ty| hashmap string ((int) -> int)] } : FuncDecl).check {} []

-- And a hashmap is itself not comparable, whatever it relates, where a list of the same things
-- would be: an association list has no canonical form, so a structural comparison would answer
-- something other than whether the two are the same map.
#guard !({ getOr with body := [lgtm| if m == m then { 1 } else { 0 }] } : FuncDecl).check {} []
#guard !({ noneBound with
  body := [lgtm| hashmap(hashmap string int, int)]
  resultType := [lgtm_ty| hashmap (hashmap string int) int] } : FuncDecl).check {} []

-- A tuple expression lists its elements in one group in parentheses, the way the *type* lists its
-- types: the group is what says how many there are, so there is an empty one to write and no
-- annotation anywhere — the elements are what the types are read off.
example : [lgtm| tuple(1, "a")] = Expression.tupleNew [.intLit 1, .stringLit "a"] := rfl
example : [lgtm| tuple("a", 1)] = Expression.tupleNew [.stringLit "a", .intLit 1] := rfl
example : [lgtm| tuple()] = Expression.tupleNew [] := rfl
example : [lgtm| tuple(1)] = Expression.tupleNew [.intLit 1] := rfl
example : [lgtm| tuple(1, "a", true)]
    = Expression.tupleNew [.intLit 1, .stringLit "a", .boolLit true] := rfl
example : [lgtm| tuple(x + 1, p.y)]
    = Expression.tupleNew [.plus (.varRef "x") (.intLit 1), .structGet (.varRef "p") "y"] := rfl
example : [lgtm| tuple(tuple(1), "a")]
    = Expression.tupleNew [.tupleNew [.intLit 1], .stringLit "a"] := rfl

-- `tuple` is a keyword, so it is no variable name inside a DSL term; outside one it is an ordinary
-- Lean identifier, which declaring it with `&` is what preserves.
example : [lgtm| var "tuple"] = Expression.varRef "tuple" := rfl

-- A read is written like a field read with an index in place of the name, binds as tightly as one,
-- and nests into the other postfix forms the same way.
example : [lgtm| t.0] = Expression.tupleGet (.varRef "t") 0 := rfl
example : [lgtm| t.1] = Expression.tupleGet (.varRef "t") 1 := rfl
example : [lgtm| t.10] = Expression.tupleGet (.varRef "t") 10 := rfl
example : [lgtm| p.t.0] = Expression.tupleGet (.structGet (.varRef "p") "t") 0 := rfl
example : [lgtm| f(1).0] = Expression.tupleGet (.app (.varRef "f") [.intLit 1]) 0 := rfl
example : [lgtm| m[k].0] = Expression.tupleGet (.hashmapGet (.varRef "m") (.varRef "k")) 0 := rfl
example : [lgtm| tuple(1, "a").0]
    = Expression.tupleGet (.tupleNew [.intLit 1, .stringLit "a"]) 0 := rfl

-- What it does not nest into is itself, because Lean's tokenizer reads `0.1` as a decimal and `0.x`
-- as an attempt at one.  Parentheses are what say which `.` is which, the same way they do for the
-- two `:`s of `[(none : int) : option int]`.
example : [lgtm| (t.0).1] = Expression.tupleGet (.tupleGet (.varRef "t") 0) 1 := rfl
example : [lgtm| (t.0).x] = Expression.structGet (.tupleGet (.varRef "t") 0) "x" := rfl

-- And what a read produces is an ordinary operand, so the looser operators take one without
-- parentheses.
example : [lgtm| t.0 + 1] = Expression.plus (.tupleGet (.varRef "t") 0) (.intLit 1) := rfl
example : [lgtm| t.0 == t.1]
    = Expression.equals (.tupleGet (.varRef "t") 0) (.tupleGet (.varRef "t") 1) := rfl
example : [lgtm| reverse tuple(1)] = Expression.listReverse (.tupleNew [.intLit 1]) := rfl

/-- The pair of its two arguments: the shortest declaration whose result type is a tuple, and the
one place the element types are the arguments' and nothing else. -/
lgtm def pair (s : string) (n : int) : tuple(string, int) :=
  tuple(s, n)

-- A tuple needs no declaration to be well formed, so this checks against no `TypeDecls` at all.
#guard pair.check {} []
#guard !({ pair with resultType := [lgtm_ty| tuple(int, string)] } : FuncDecl).check {} []
#guard !({ pair with resultType := [lgtm_ty| tuple(string)] } : FuncDecl).check {} []
#guard !({ pair with resultType := [lgtm_ty| list string] } : FuncDecl).check {} []

/-- The first half of a pair, which is the other half: a value read out of a tuple rather than put
into one. -/
lgtm def fst (t : tuple(string, int)) : string :=
  t.0

#guard fst.check {} []
#guard ({ fst with body := [lgtm| t.1], resultType := .int } : FuncDecl).check {} []

-- An index past the end is ill typed, which is what makes the index a literal: the type at a
-- position that is not known until something runs is a type nothing could report.
#guard !({ fst with body := [lgtm| t.2] } : FuncDecl).check {} []
#guard !({ fst with body := [lgtm| t.1] } : FuncDecl).check {} []

-- A tuple is comparable exactly when everything in it is, so a pair of a map is not and a pair of
-- its two types is: what `Ty.comparable` turns a hashmap down for is the order its bindings are
-- carried in, which converting does not escape.
#guard ({ fst with
  body := [lgtm| if t == t then { t.0 } else { t.0 }] } : FuncDecl).check {} []
#guard !({ fst with
  parameters := [("t", [lgtm_ty| tuple(string, hashmap string int)])]
  body := [lgtm| if t == t then { t.0 } else { t.0 }] } : FuncDecl).check {} []

/-- The bindings of a map as a list of pairs, which is the type `toList` gives one: the form a
`tuple` is in the IR for. -/
lgtm def bindings (m : hashmap string int) : list tuple(string, int) :=
  toList m

#guard bindings.check {} []
#guard !({ bindings with resultType := [lgtm_ty| list tuple(int, string)] } : FuncDecl).check {} []
