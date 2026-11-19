module

import LgtmDeepLean.Lang.Syntax
meta import LgtmDeepLean.Lang.Syntax

/-! # Tests for the surface syntax

What `[lgtm_ty| ...]`, `[lgtm| ...]`, `@[lgtm] def`, `@[lgtm] structure`, and `@[lgtm] inductive`
elaborate to: each form against the constructors it describes, the precedences that decide how a
term without parentheses is read, and the declarations the commands build — checked, where it is the
point, with `FuncDecl.check`. -/

-- Types elaborate to the constructors they describe, `fn` taking all its parameters at once.
example : [lgtm_ty| int] = Ty.int :=
  rfl

example : [lgtm_ty| bool] = Ty.bool :=
  rfl

example : [lgtm_ty| list bool] = Ty.list .bool :=
  rfl

example : [lgtm_ty| (bool, int) -> bool] = Ty.fn [.bool, .int] .bool :=
  rfl

example : [lgtm_ty| list string] = Ty.list .string :=
  rfl

example : [lgtm_ty| list list int] = Ty.list (.list .int) :=
  rfl

example : [lgtm_ty| (int, string) -> int] = Ty.fn [.int, .string] .int :=
  rfl

example : [lgtm_ty| () -> int] = Ty.fn [] .int :=
  rfl

example : [lgtm_ty| list((int) -> int)] = Ty.list (.fn [.int] .int) :=
  rfl

example : [lgtm_ty| (int) -> (string) -> int] = Ty.fn [.int] (.fn [.string] .int) :=
  rfl

-- Leaves.
example : [lgtm| x] = Expression.varRef "x" :=
  rfl

example : [lgtm| var"my-var"] = Expression.varRef "my-var" :=
  rfl

example : [lgtm| 3] = Expression.intLit 3 :=
  rfl

example : [lgtm| "hi"] = Expression.stringLit "hi" :=
  rfl

example : [lgtm| true] = Expression.boolLit true :=
  rfl

example : [lgtm| false] = Expression.boolLit false :=
  rfl

-- `true` and `false` are keywords, so neither is a variable name inside a DSL term.  Outside one
-- they are Lean's own `true` and `false`, which declaring them with `&` is what preserves.
example : [lgtm| var"true"] = Expression.varRef "true" :=
  rfl

example : (true : Bool) = Bool.true :=
  rfl

-- A `bool` literal is an ordinary operand: it goes in a list, in a call, and in a conditional.
example :
    [lgtm| [true, false : bool]] =
      Expression.lcons (.boolLit true) (.lcons (.boolLit false) (.lnil .bool)) :=
  rfl

example : [lgtm| f(true, 1)] = Expression.app (.varRef "f") [.boolLit true, .intLit 1] :=
  rfl

example : [lgtm| true :: bs] = Expression.lcons (.boolLit true) (.varRef "bs") :=
  rfl

example : [lgtm| let b := true; b] = Expression.let_ "b" (.boolLit true) (.varRef "b") :=
  rfl

example : [lgtm| fun(b : bool) => true] = Expression.lam [("b", .bool)] (.boolLit true) :=
  rfl

-- Arithmetic is left-associative, and parentheses group as written.
example : [lgtm| x + 1] = Expression.plus (.varRef "x") (.intLit 1) :=
  rfl

example : [lgtm| x + y - 1] = Expression.minus (.plus (.varRef "x") (.varRef "y")) (.intLit 1) :=
  rfl

example : [lgtm| x + (y - 1)] = Expression.plus (.varRef "x") (.minus (.varRef "y") (.intLit 1)) :=
  rfl

-- `min` and `max` are prefix keywords taking two operands, each as tight as `reverse`'s one, so
-- neither reads past an operand of its own and both nest without parentheses.
example : [lgtm| min x y] = Expression.min (.varRef "x") (.varRef "y") :=
  rfl

example : [lgtm| max x y] = Expression.max (.varRef "x") (.varRef "y") :=
  rfl

example : [lgtm| min 1 f(2)] = Expression.min (.intLit 1) (.app (.varRef "f") [.intLit 2]) :=
  rfl

example : [lgtm| max length xs 0] = Expression.max (.listLength (.varRef "xs")) (.intLit 0) :=
  rfl

example : [lgtm| min x max y z] = Expression.min (.varRef "x") (.max (.varRef "y") (.varRef "z")) :=
  rfl

-- Binding tighter than `+` is what puts the arithmetic outside rather than in an operand, and
-- parentheses are what reach back in.
example : [lgtm| min x y + 1] = Expression.plus (.min (.varRef "x") (.varRef "y")) (.intLit 1) :=
  rfl

example : [lgtm| max (x + 1) y] = Expression.max (.plus (.varRef "x") (.intLit 1)) (.varRef "y") :=
  rfl

example :
    [lgtm| min x y <= max x y] =
      Expression.le (.min (.varRef "x") (.varRef "y")) (.max (.varRef "x") (.varRef "y")) :=
  rfl

-- A variable of either name takes the escape hatch, the way `reverse` and `length` do.
example : [lgtm| var"min"] = Expression.varRef "min" :=
  rfl

example : [lgtm| var"max"] = Expression.varRef "max" :=
  rfl

-- `::` binds looser than `+`, so the arithmetic happens to the element rather than the list.
example : [lgtm| x :: xs] = Expression.lcons (.varRef "x") (.varRef "xs") :=
  rfl

example : [lgtm| x + 1 :: xs] = Expression.lcons (.plus (.varRef "x") (.intLit 1)) (.varRef "xs") :=
  rfl

-- `==` is looser than both, so each of its operands is as much as can be read before it.
example : [lgtm| x == y] = Expression.equals (.varRef "x") (.varRef "y") :=
  rfl

example : [lgtm| x + 1 == y] = Expression.equals (.plus (.varRef "x") (.intLit 1)) (.varRef "y") :=
  rfl

example :
    [lgtm| x :: xs == ys] =
      Expression.equals (.lcons (.varRef "x") (.varRef "xs")) (.varRef "ys") :=
  rfl

example :
    [lgtm| reverse xs == ys] = Expression.equals (.listReverse (.varRef "xs")) (.varRef "ys") :=
  rfl

example :
    [lgtm| f(1) == g(2)] =
      Expression.equals (.app (.varRef "f") [.intLit 1]) (.app (.varRef "g") [.intLit 2]) :=
  rfl

example :
    [lgtm| p.x == q.x] =
      Expression.equals (.structGet (.varRef "p") "x") (.structGet (.varRef "q") "x") :=
  rfl

-- Parentheses are what chain comparisons, since `==` is non-associative; and a comparison is an
-- operand anywhere a `bool` is one.
example :
    [lgtm| (x == y) == b] = Expression.equals (.equals (.varRef "x") (.varRef "y")) (.varRef "b") :=
  rfl

example :
    [lgtm| if x == y then (1) else (2)] =
      Expression.ite (.equals (.varRef "x") (.varRef "y")) (.intLit 1) (.intLit 2) :=
  rfl

example :
    [lgtm| let e := x == y; e] =
      Expression.let_ "e" (.equals (.varRef "x") (.varRef "y")) (.varRef "e") :=
  rfl

example :
    [lgtm| fun(q : int) => q == n] =
      Expression.lam [("q", .int)] (.equals (.varRef "q") (.varRef "n")) :=
  rfl

example : [lgtm| f(x == y)] = Expression.app (.varRef "f") [.equals (.varRef "x") (.varRef "y")] :=
  rfl

example :
    [lgtm| [x == y, true : bool]] =
      Expression.lcons (.equals (.varRef "x") (.varRef "y"))
        (.lcons (.boolLit true) (.lnil .bool)) :=
  rfl

-- `<` and `<=` sit at `==`'s level, so each reads as much on either side as a `==` would.
example : [lgtm| x < y] = Expression.lt (.varRef "x") (.varRef "y") :=
  rfl

example : [lgtm| x <= y] = Expression.le (.varRef "x") (.varRef "y") :=
  rfl

example : [lgtm| x + 1 < y] = Expression.lt (.plus (.varRef "x") (.intLit 1)) (.varRef "y") :=
  rfl

example : [lgtm| x < y + 1] = Expression.lt (.varRef "x") (.plus (.varRef "y") (.intLit 1)) :=
  rfl

example : [lgtm| length xs <= 0] = Expression.le (.listLength (.varRef "xs")) (.intLit 0) :=
  rfl

example :
    [lgtm| f(1) <= g(2)] =
      Expression.le (.app (.varRef "f") [.intLit 1]) (.app (.varRef "g") [.intLit 2]) :=
  rfl

example :
    [lgtm| p.x < q.x] =
      Expression.lt (.structGet (.varRef "p") "x") (.structGet (.varRef "q") "x") :=
  rfl

example :
    [lgtm| x :: xs <= ys] = Expression.le (.lcons (.varRef "x") (.varRef "xs")) (.varRef "ys") :=
  rfl

-- `<=` is one token: the two characters are read together, so this is an ordering and not a
-- comparison against something starting with `=`.
example : [lgtm| x <= y] ≠ Expression.lt (.varRef "x") (.varRef "y") := by simp

-- None of the three comparisons associates, so parentheses are what nests one in another — and a
-- comparison is an operand anywhere a `bool` is one.
example :
    [lgtm| (x < y) == b] = Expression.equals (.lt (.varRef "x") (.varRef "y")) (.varRef "b") :=
  rfl

example :
    [lgtm| (x < y) == (x <= y)] =
      Expression.equals (.lt (.varRef "x") (.varRef "y")) (.le (.varRef "x") (.varRef "y")) :=
  rfl

example :
    [lgtm| if x <= y then (1) else (2)] =
      Expression.ite (.le (.varRef "x") (.varRef "y")) (.intLit 1) (.intLit 2) :=
  rfl

example :
    [lgtm| let b := x < y; b] =
      Expression.let_ "b" (.lt (.varRef "x") (.varRef "y")) (.varRef "b") :=
  rfl

example :
    [lgtm| fun(q : int) => q <= n] =
      Expression.lam [("q", .int)] (.le (.varRef "q") (.varRef "n")) :=
  rfl

example : [lgtm| f(x < y)] = Expression.app (.varRef "f") [.lt (.varRef "x") (.varRef "y")] :=
  rfl

-- `&&` and `||` are looser than `==`, which is what lets a comparison be an operand of either
-- without parentheses, and `||` is the looser of the two.
example : [lgtm| b && c] = Expression.boolAnd (.varRef "b") (.varRef "c") :=
  rfl

example : [lgtm| b || c] = Expression.boolOr (.varRef "b") (.varRef "c") :=
  rfl

example :
    [lgtm| x == y && b] = Expression.boolAnd (.equals (.varRef "x") (.varRef "y")) (.varRef "b") :=
  rfl

example :
    [lgtm| b && x == y] = Expression.boolAnd (.varRef "b") (.equals (.varRef "x") (.varRef "y")) :=
  rfl

example :
    [lgtm| length xs == 0 || b] =
      Expression.boolOr (.equals (.listLength (.varRef "xs")) (.intLit 0)) (.varRef "b") :=
  rfl

example :
    [lgtm| x <= y && y <= z] =
      Expression.boolAnd (.le (.varRef "x") (.varRef "y")) (.le (.varRef "y") (.varRef "z")) :=
  rfl

example :
    [lgtm| x < y || x == y] =
      Expression.boolOr (.lt (.varRef "x") (.varRef "y")) (.equals (.varRef "x") (.varRef "y")) :=
  rfl

example :
    [lgtm| a || b && c] = Expression.boolOr (.varRef "a") (.boolAnd (.varRef "b") (.varRef "c")) :=
  rfl

example :
    [lgtm| a && b || c] = Expression.boolOr (.boolAnd (.varRef "a") (.varRef "b")) (.varRef "c") :=
  rfl

example :
    [lgtm| (a || b) && c] =
      Expression.boolAnd (.boolOr (.varRef "a") (.varRef "b")) (.varRef "c") :=
  rfl

-- Both are left-associative, unlike `==`, which takes parentheses to chain at all.
example :
    [lgtm| a && b && c] = Expression.boolAnd (.boolAnd (.varRef "a") (.varRef "b")) (.varRef "c") :=
  rfl

example :
    [lgtm| a || b || c] = Expression.boolOr (.boolOr (.varRef "a") (.varRef "b")) (.varRef "c") :=
  rfl

example :
    [lgtm| a && (b && c)] =
      Expression.boolAnd (.varRef "a") (.boolAnd (.varRef "b") (.varRef "c")) :=
  rfl

-- What they produce is a `bool` like any other, so every form that reads one reads these: a
-- condition, an operand of another one, a call's argument, a list of them.
example :
    [lgtm| if b && c then (1) else (2)] =
      Expression.ite (.boolAnd (.varRef "b") (.varRef "c")) (.intLit 1) (.intLit 2) :=
  rfl

example : [lgtm| f(b || c)] = Expression.app (.varRef "f") [.boolOr (.varRef "b") (.varRef "c")] :=
  rfl

example :
    [lgtm| fun(b : bool) => b && true] =
      Expression.lam [("b", .bool)] (.boolAnd (.varRef "b") (.boolLit true)) :=
  rfl

example :
    [lgtm| let e := b || c; e] =
      Expression.let_ "e" (.boolOr (.varRef "b") (.varRef "c")) (.varRef "e") :=
  rfl

example :
    [lgtm| [b && c, true : bool]] =
      Expression.lcons (.boolAnd (.varRef "b") (.varRef "c"))
        (.lcons (.boolLit true) (.lnil .bool)) :=
  rfl

-- A list literal is right-nested `lcons` onto the `lnil` its annotation gives.
example : [lgtm| [ : int]] = Expression.lnil .int :=
  rfl

example : [lgtm| [1 : int]] = Expression.lcons (.intLit 1) (.lnil .int) :=
  rfl

example :
    [lgtm| ["!", s : string]] =
      Expression.lcons (.stringLit "!") (.lcons (.varRef "s") (.lnil .string)) :=
  rfl

-- A `match` on a list is the two cases it has, which is a `listMatch` rather than an `indMatch`: the
-- empty case computes with nothing and the other binds the head and the tail the list was built
-- from.  The alternatives are written with the tokens a list is written with, which is what tells
-- this reading of a `match` from the other two.
example :
    [lgtm| match xs with | [] => 0 | hd :: tl => hd] =
      Expression.listMatch (.varRef "xs") (.intLit 0) "hd" "tl" (.varRef "hd") :=
  rfl

example :
    [lgtm| match xs with | [] => 0 | hd :: tl => length tl] =
      Expression.listMatch (.varRef "xs") (.intLit 0) "hd" "tl" (.listLength (.varRef "tl")) :=
  rfl

example :
    [lgtm| match f(1) with | [] => "" | s :: rest => s] =
      Expression.listMatch (.app (.varRef "f") [.intLit 1]) (.stringLit "") "s" "rest"
        (.varRef "s") :=
  rfl

example :
    [lgtm| match x :: xs with | [] => 0 | hd :: tl => hd] =
      Expression.listMatch (.lcons (.varRef "x") (.varRef "xs")) (.intLit 0) "hd" "tl"
        (.varRef "hd") :=
  rfl

-- An alternative's expression extends as far right as it can here too, so a match nested in one
-- needs no parentheses and one used as an operand does.
example :
    [lgtm| match xs with | [] => 0 | hd :: tl => match tl with | [] => 1 | a :: b => a] =
      Expression.listMatch (.varRef "xs") (.intLit 0) "hd" "tl"
        (.listMatch (.varRef "tl") (.intLit 1) "a" "b" (.varRef "a")) :=
  rfl

example :
    [lgtm| (match xs with | [] => 0 | hd :: tl => hd) + 1] =
      Expression.plus (.listMatch (.varRef "xs") (.intLit 0) "hd" "tl" (.varRef "hd"))
        (.intLit 1) :=
  rfl

-- A match on what a list form produced is a match like any other, since those produce lists.
example :
    [lgtm| match reverse xs with | [] => 0 | hd :: tl => hd] =
      Expression.listMatch (.listReverse (.varRef "xs")) (.intLit 0) "hd" "tl" (.varRef "hd") :=
  rfl

-- The alternatives of the other two readings are unchanged: neither mentions `[]` or `::`, so a
-- `match` on an inductive type or on an option parses as it did.
example :
    [lgtm| match c with | Red => 0 | Rgb(r, g, b) => r] =
      Expression.indMatch (.varRef "c")
        [("Red", [], .intLit 0), ("Rgb", ["r", "g", "b"], .varRef "r")] :=
  rfl

example :
    [lgtm| match o with | none => 0 | some(x) => x] =
      Expression.optionMatch (.varRef "o") (.intLit 0) "x" (.varRef "x") :=
  rfl

/-- The head of `xs`, and `d` when it has none: the two cases a list has and the match between them,
which is what a declaration reading one element off a list looks like. -/
@[lgtm] def headOr as"head-or"(xs : list int)(d : int) : int :=
  match xs with | [] => d | hd :: tl => hd

-- A list needs no declaration to be well formed, so this checks against no `TypeDecls` at all.
#guard (headOr.check {} []).isOk

-- The two cases have to share a type, and the names bound stand at the element type and at the
-- list's own — so `hd` is an `int` and `tl` a `list int` because the parameter is a `list int`.
#guard
  !(({ headOr with body := [lgtm| match xs with | [] => d | hd :: tl => "a"] } : FuncDecl).check {}
        []).isOk

#guard
  !(({ headOr with body := [lgtm| match xs with | [] => d | hd :: tl => tl] } : FuncDecl).check {}
        []).isOk

#guard
  (({ headOr with
            body := [lgtm| match xs with | [] => xs | hd :: tl => tl]
            resultType := [lgtm_ty| list int] } :
          FuncDecl).check
      {} []).isOk

-- And the scrutinee has to be a list: an option is not one, however much the match looks like it
-- could take one apart.
#guard
  !(({ headOr with parameters := [("xs", [lgtm_ty| option int]), ("d", .int)] } : FuncDecl).check {}
        []).isOk

-- Both alternatives are required and in the order `listMatch` holds them, since there is nothing
-- else a `match` written with these alternatives could have meant.
/-- error: a match on a list takes `[]` first and `::` second -/
#guard_msgs (error) in
#check [lgtm| match xs with | hd :: tl => hd | [] => 0]

/-- error: a match on a list has two alternatives: `| [] => ... | hd :: tl => ...` -/
#guard_msgs (error) in
#check [lgtm| match xs with | [] => 0]

/-- error: a match on a list has two alternatives: `| [] => ... | hd :: tl => ...` -/
#guard_msgs (error) in
#check [lgtm| match xs with | hd :: tl => hd]

/-- error: a match on a list has two alternatives: `| [] => ... | hd :: tl => ...` -/
#guard_msgs (error) in
#check [lgtm| match xs with | [] => 0 | [] => 1]

-- The names are in scope in the case that binds them and nowhere else, the way `some(x)`'s is.
/-- error: no variable named 'hd' is in scope -/
#guard_msgs (error) in
@[lgtm] def headOfEmpty as"head-of-empty"(xs : list int) : int :=
  match xs with | [] => hd | hd :: tl => hd

-- `reverse` is a form of its own, not a call, so it takes its operand without parentheses.
example : [lgtm| reverse xs] = Expression.listReverse (.varRef "xs") :=
  rfl

example : [lgtm| reverse(x :: xs)] = Expression.listReverse (.lcons (.varRef "x") (.varRef "xs")) :=
  rfl

example : [lgtm| reverse reverse xs] = Expression.listReverse (.listReverse (.varRef "xs")) :=
  rfl

-- `length` is written like `reverse`, and binds as tightly, so it takes one operand and no more.
example : [lgtm| length xs] = Expression.listLength (.varRef "xs") :=
  rfl

example : [lgtm| length(x :: xs)] = Expression.listLength (.lcons (.varRef "x") (.varRef "xs")) :=
  rfl

example :
    [lgtm| length[1, 2 : int]] =
      Expression.listLength (.lcons (.intLit 1) (.lcons (.intLit 2) (.lnil .int))) :=
  rfl

example : [lgtm| length reverse xs] = Expression.listLength (.listReverse (.varRef "xs")) :=
  rfl

-- Binding tighter than `+` and `==` is what makes an `int` out of a length usable in place.
example : [lgtm| length xs + 1] = Expression.plus (.listLength (.varRef "xs")) (.intLit 1) :=
  rfl

example :
    [lgtm| length xs == length ys] =
      Expression.equals (.listLength (.varRef "xs")) (.listLength (.varRef "ys")) :=
  rfl

-- A variable of a keyword's name takes the escape hatch, the way `reverse` and `toList` do.
example : [lgtm| var"length"] = Expression.varRef "length" :=
  rfl

-- Application takes all its arguments at once, and nests to the left.
example : [lgtm| f(x)] = Expression.app (.varRef "f") [.varRef "x"] :=
  rfl

example : [lgtm| f(1, "a")] = Expression.app (.varRef "f") [.intLit 1, .stringLit "a"] :=
  rfl

example : [lgtm| f()] = Expression.app (.varRef "f") [] :=
  rfl

example : [lgtm| f(1)(2)] = Expression.app (.app (.varRef "f") [.intLit 1]) [.intLit 2] :=
  rfl

-- A `lam`'s parameters are IR names paired with their annotations.
example : [lgtm| fun(x : int) => x] = Expression.lam [("x", .int)] (.varRef "x") :=
  rfl

example :
    [lgtm| fun(x : int)(y : string) => y] =
      Expression.lam [("x", .int), ("y", .string)] (.varRef "y") :=
  rfl

example : [lgtm| fun => 1] = Expression.lam [] (.intLit 1) :=
  rfl

-- A lambda's body extends as far right as it can, so the `+` is inside it.
example :
    [lgtm| fun(x : int) => x + 1] =
      Expression.lam [("x", .int)] (.plus (.varRef "x") (.intLit 1)) :=
  rfl

-- A `let` names the expression it binds, which carries no annotation.
example : [lgtm| let x := 1; x] = Expression.let_ "x" (.intLit 1) (.varRef "x") :=
  rfl

example :
    [lgtm| let x := y + 1; x + x] =
      Expression.let_ "x" (.plus (.varRef "y") (.intLit 1)) (.plus (.varRef "x") (.varRef "x")) :=
  rfl

-- The body extends as far right as it can, so `let`s chain without parentheses and a `let` inside a
-- lambda swallows the rest of the body.
example :
    [lgtm| let x := 1; let y := 2; x + y] =
      Expression.let_ "x" (.intLit 1) (.let_ "y" (.intLit 2) (.plus (.varRef "x") (.varRef "y"))) :=
  rfl

example :
    [lgtm| fun(n : int) => let m := n + 1; m + m] =
      Expression.lam [("n", .int)]
        (.let_ "m" (.plus (.varRef "n") (.intLit 1)) (.plus (.varRef "m") (.varRef "m"))) :=
  rfl

-- The bound expression stops at `;`, so a `fun` or a call on the right of the `:=` needs no
-- parentheses either.
example :
    [lgtm| let f := fun(x : int) => x; f(1)] =
      Expression.let_ "f" (.lam [("x", .int)] (.varRef "x")) (.app (.varRef "f") [.intLit 1]) :=
  rfl

example :
    [lgtm| let xs := reverse ys; x :: xs] =
      Expression.let_ "xs" (.listReverse (.varRef "ys")) (.lcons (.varRef "x") (.varRef "xs")) :=
  rfl

-- Parenthesizing the body is what puts something after the `let` rather than inside it.
example :
    [lgtm| (let x := 1; x) + 2] =
      Expression.plus (.let_ "x" (.intLit 1) (.varRef "x")) (.intLit 2) :=
  rfl

-- A conditional is its condition and its two braced branches.
example : [lgtm| if b then (1) else (2)] = Expression.ite (.varRef "b") (.intLit 1) (.intLit 2) :=
  rfl

example :
    [lgtm| if true then (1) else (2)] = Expression.ite (.boolLit true) (.intLit 1) (.intLit 2) :=
  rfl

example :
    [lgtm| if b then (true) else (false)] =
      Expression.ite (.varRef "b") (.boolLit true) (.boolLit false) :=
  rfl

example :
    [lgtm| if f(x) then (x + 1) else (x - 1)] =
      Expression.ite (.app (.varRef "f") [.varRef "x"]) (.plus (.varRef "x") (.intLit 1))
        (.minus (.varRef "x") (.intLit 1)) :=
  rfl

-- The braces end the branches, so a conditional is an ordinary operand: the `+ 1` below applies to
-- the whole of it rather than to its second branch, and neither branch needs parentheses.
example :
    [lgtm| if b then (1) else (2) + 1] =
      Expression.plus (.ite (.varRef "b") (.intLit 1) (.intLit 2)) (.intLit 1) :=
  rfl

example :
    [lgtm| if b then (let x := 1; x) else (match c with | Red => 0)] =
      Expression.ite (.varRef "b") (.let_ "x" (.intLit 1) (.varRef "x"))
        (.indMatch (.varRef "c") [("Red", [], .intLit 0)]) :=
  rfl

example :
    [lgtm| f(if b then (1) else (2))] =
      Expression.app (.varRef "f") [.ite (.varRef "b") (.intLit 1) (.intLit 2)] :=
  rfl

-- And conditionals nest, in the branches and in the condition alike.
example :
    [lgtm| if b then (if c then (1) else (2)) else (3)] =
      Expression.ite (.varRef "b") (.ite (.varRef "c") (.intLit 1) (.intLit 2)) (.intLit 3) :=
  rfl

example :
    [lgtm| if if b then (c) else (d) then (1) else (2)] =
      Expression.ite (.ite (.varRef "b") (.varRef "c") (.varRef "d")) (.intLit 1) (.intLit 2) :=
  rfl

-- Identifiers are IR names, never Lean ones: `n` below is a `varRef`, not this Lean `n`.
private def n : Expression :=
  .intLit 99

example : [lgtm| n] = Expression.varRef "n" :=
  rfl

-- Splicing is how a Lean term gets in.
example : [lgtm| ~(n) + 1] = Expression.plus (.intLit 99) (.intLit 1) :=
  rfl

example : [lgtm_ty| list~(Ty.int)] = Ty.list .int :=
  rfl

/-- Add `x` to one less than `y`. -/
@[lgtm] def addPred as"add-pred"(x : int)(y : int) : int := x + (y - 1)

-- The command builds the `FuncDecl` field by field: the doc comment, the `as` name, the parameters
-- in order, the body, and the result type.
example :
    addPred =
      { docstring := "Add `x` to one less than `y`."
        name := "add-pred"
        parameters := [("x", .int), ("y", .int)]
        body := .plus (.varRef "x") (.minus (.varRef "y") (.intLit 1))
        resultType := .int } :=
  rfl

-- And what it builds type checks, which is the point of writing it this way.
#guard (addPred.check {} []).isOk

/-- Put `s` after an exclamation mark. -/
@[lgtm] def bang(s : string) : list string := ["!", s : string]

-- With no `as`, the IR name is the Lean name.
example : bang.name = "bang" :=
  rfl

#guard (bang.check {} []).isOk

@[lgtm] def applyTo as"apply-to"(g : (int) -> int)(x : int) : int := g(x)

#guard (applyTo.check {} []).isOk

/-- Build a function that adds `n` to its argument. -/
@[lgtm] def adder(n : int) : (int) -> int := fun(m : int) => n + m

#guard (adder.check {} []).isOk

/-- Reverse `xs` with `x` on the front. -/
@[lgtm] def revCons as"rev-cons"(x : int)(xs : list int) : list int := reverse(x :: xs)

#guard (revCons.check {} []).isOk

/-- Every element of `xs` with one added to it.  The function takes one parameter, at the list's
element type, which is what tells a mapping over a list from one over a hashmap where the function
is written out. -/
@[lgtm] def bumpAll as "bump-all" (xs : list int) : list int :=
  map xs (fun (x : int) => x + 1)

#guard (bumpAll.check {} []).isOk

example :
    bumpAll.body = Expression.listMap (.varRef "xs") (.lam [("x", .int)]
      (.plus (.varRef "x") (.intLit 1))) :=
  rfl

-- The element type is the one thing a mapping over a list does not carry through, so what the
-- function returns is what the result is a list of and the declaration has to say so.
#guard (({ bumpAll with
  body := [lgtm| map xs (fun (x : int) => "a")]
  resultType := [lgtm_ty| list string] } : FuncDecl).check {} []).isOk

#guard !(({ bumpAll with body := [lgtm| map xs (fun (x : int) => "a")] } : FuncDecl).check {} []).isOk

-- The function is held to the element type, and to taking one parameter: a two-parameter function is
-- a hashmap's mapping's, and no mapping over a list accepts one.
#guard !(({ bumpAll with body := [lgtm| map xs (fun (x : string) => 1)] } : FuncDecl).check {} []).isOk

#guard !(({ bumpAll with body := [lgtm| map xs (fun (x : int) (y : int) => 1)] }
  : FuncDecl).check {} []).isOk

-- An operand that is neither a list nor a hashmap is read as a list's mapping, since a hashmap is
-- the one type the other reading is deduced from, and the message names both the forms could have
-- been written over.
/-- error: `map` needs a list or a hashmap, but its first operand has type int -/
#guard_msgs (error) in
@[lgtm] def chkMapInt(n : int) : list int :=
  map n (fun (x : int) => x)

/-- Whether `xs` is empty or is `ys`: the shortest declaration the two boolean operators are in,
and the one place their being looser than `==` is what keeps a comparison on either side
unparenthesized. -/
@[lgtm] def emptyOrEqual as"empty-or-equal"(xs : list int)(ys : list int) : bool :=
  length xs == 0 || xs == ys

#guard (emptyOrEqual.check {} []).isOk

#guard
  (({ emptyOrEqual with body := [lgtm| length xs == 0 && xs == ys] } : FuncDecl).check {} []).isOk

-- Both operands have to be `bool`s, and what comes out is one whatever they were about: there is no
-- truthiness to read an `int` as, the same way a conditional's condition has none.
#guard !(({ emptyOrEqual with body := [lgtm| length xs || xs == ys] } : FuncDecl).check {} []).isOk

#guard !(({ emptyOrEqual with body := [lgtm| xs == ys && length xs] } : FuncDecl).check {} []).isOk

#guard !(({ emptyOrEqual with resultType := [lgtm_ty| int] } : FuncDecl).check {} []).isOk

/-- Twice one more than `n`. -/
@[lgtm] def letDouble as"let-double"(n : int) : int := let m := n + 1; m + m

#guard (letDouble.check {} []).isOk

/-- `x` when `b`, and `y` otherwise. -/
@[lgtm] def pick(b : bool)(x : int)(y : int) : int := if b then (x) else (y)

#guard (pick.check {} []).isOk

-- A `bool` is a type like any other, so a declaration can return one and a list can hold them, and
-- a literal is where one comes from when no parameter has one.
@[lgtm] def firstOf as"first-of"(b : bool)(bs : list bool) : list bool := b :: bs

#guard (firstOf.check {} []).isOk

/-- The two literals, which is the shortest declaration that returns a `bool`. -/
@[lgtm] def yes : bool := true

#guard (yes.check {} []).isOk

#guard !(({ yes with body := [lgtm| 1] } : FuncDecl).check {} []).isOk

#guard !(({ yes with resultType := [lgtm_ty| int] } : FuncDecl).check {} []).isOk

-- So a `bool` no longer has to be passed in: a conditional can be written with its condition spelled
-- out, and a list of them needs no parameter either.
@[lgtm] def flags : list bool := [true, false, true : bool]

#guard (flags.check {} []).isOk

@[lgtm] def pickFirst as"pick-first"(x : int)(y : int) : int := if true then (x) else (y)

#guard (pickFirst.check {} []).isOk

#guard !(({ pickFirst with body := [lgtm| if 1 then (x) else (y)] } : FuncDecl).check {} []).isOk

/-- Whether `x` and `y` are the same, which is the other way a declaration returns a `bool`. -/
@[lgtm] def same(x : int)(y : int) : bool := x == y

#guard (same.check {} []).isOk

-- The operands have to share a type, the result is a `bool` and not the type compared, and a
-- function is the one thing there is no comparing: a parameter of function type cannot be an operand
-- and neither can a list of them.
#guard !(({ same with body := [lgtm| x == "a"] } : FuncDecl).check {} []).isOk

#guard !(({ same with resultType := [lgtm_ty| int] } : FuncDecl).check {} []).isOk

private def fnTy : Ty :=
  [lgtm_ty| (int) -> int]

/-- `same` comparing two functions, which is the one thing a comparison cannot reach the bottom of. -/
private def sameFns : FuncDecl :=
  { same with
    parameters := [("g", fnTy), ("h", fnTy)], body := [lgtm| g == h] }

/-- And comparing two lists of them, which is no more comparable than its elements are. -/
private def sameFnLists : FuncDecl :=
  { sameFns with parameters := [("g", .list fnTy), ("h", .list fnTy)] }

#guard !(sameFns.check {} []).isOk

#guard !(sameFnLists.check {} []).isOk

-- Every other type is comparable, declared ones included, and a comparison goes where a `bool` goes.
#guard
  (({ same with parameters := [("x", [lgtm_ty| list string]), ("y", [lgtm_ty| list string])] } :
          FuncDecl).check
      {} []).isOk

#guard
  (({ same with parameters := [("x", [lgtm_ty| bool]), ("y", [lgtm_ty| bool])] } : FuncDecl).check
      {} []).isOk

#guard (({ pick with body := [lgtm| if x == y then (x) else (y)] } : FuncDecl).check {} []).isOk

-- A declaration with no parameters is fine, and so is one that returns a function.
@[lgtm] def three : int := 3

#guard (three.check {} []).isOk

-- A declaration is called by its IR name, and a dotted one is the whole name rather than a field
-- read: `Nested.one` is the declaration below, which is how one declaration calls another.  A
-- nullary one still takes the parentheses — `Ty.fn [] .int` is not `Ty.int`.
@[lgtm] def Nested.one : int := 1

example : [lgtm| Nested.one] = Expression.varRef "Nested.one" :=
  rfl

example : [lgtm| Nested.one()] = Expression.app (.varRef "Nested.one") [] :=
  rfl

#guard
  (({ three with body := [lgtm| Nested.one()] } : FuncDecl).check {}
      [("Nested.one", Nested.one)]).isOk

#guard
  !(({ three with body := [lgtm| Nested.one] } : FuncDecl).check {}
        [("Nested.one", Nested.one)]).isOk

-- A dotted name no declaration has taken is a variable and one field read per component, and the
-- postfix `.` is what reads a field off a name that is taken.
example : [lgtm| Nested.two] = Expression.structGet (.varRef "Nested") "two" :=
  rfl

example : [lgtm| (var"Nested.one").x] = Expression.structGet (.varRef "Nested.one") "x" :=
  rfl

-- `@[lgtm] private def` makes the Lean declaration private; the `FuncDecl` it builds is the same.
/-- One more than `x`. -/
@[lgtm] private def succ as"succ-one"(x : int) : int := x + 1

example : succ.name = "succ-one" :=
  rfl

example : succ.docstring = "One more than `x`." :=
  rfl

#guard (succ.check {} []).isOk

-- The DSL builds ill-typed programs as readily as well-typed ones; checking is still what rejects
-- them.
#guard !(({ three with body := [lgtm| 1 + "a"] } : FuncDecl).check {} []).isOk

#guard !(({ revCons with body := [lgtm| reverse x] } : FuncDecl).check {} []).isOk

#guard !(({ pick with body := [lgtm| if x then (x) else (y)] } : FuncDecl).check {} []).isOk

#guard !(({ pick with body := [lgtm| if b then (x) else ("a")] } : FuncDecl).check {} []).isOk

/-! ### Structs -/

-- A struct type is written with its name, which is a type like any other: it nests under `list`,
-- appears in a function type, and can be spelled with a string when it is not a Lean identifier.
example : [lgtm_ty| struct Point] = Ty.struct "Point" :=
  rfl

example : [lgtm_ty| struct"my-struct"] = Ty.struct "my-struct" :=
  rfl

example : [lgtm_ty| list struct Point] = Ty.list (.struct "Point") :=
  rfl

example : [lgtm_ty| (struct Point) -> struct Point] = Ty.fn [.struct "Point"] (.struct "Point") :=
  rfl

-- `new` gives each field an expression, in the order written.
example :
    [lgtm| new Point{x = 1, y = 2}] =
      Expression.structNew "Point" [("x", .intLit 1), ("y", .intLit 2)] :=
  rfl

example : [lgtm| new"my-struct"{f = n}] = Expression.structNew "my-struct" [("f", .varRef "n")] :=
  rfl

example : [lgtm| new Point{}] = Expression.structNew "Point" [] :=
  rfl

example :
    [lgtm| new Point{x = f(1) + 1, y = [2 : int]}] =
      Expression.structNew "Point"
        [("x", .plus (.app (.varRef "f") [.intLit 1]) (.intLit 1)),
          ("y", .lcons (.intLit 2) (.lnil .int))] :=
  rfl

-- A field read of a bare name is a dotted identifier, which is one `structGet` per component.
example : [lgtm| p.x] = Expression.structGet (.varRef "p") "x" :=
  rfl

example : [lgtm| p.origin.x] = Expression.structGet (.structGet (.varRef "p") "origin") "x" :=
  rfl

-- A field read of anything else is the postfix `.`, and the two nest into each other.
example : [lgtm| f(1).x] = Expression.structGet (.app (.varRef "f") [.intLit 1]) "x" :=
  rfl

example :
    [lgtm| f(1).origin.x] =
      Expression.structGet (.structGet (.app (.varRef "f") [.intLit 1]) "origin") "x" :=
  rfl

example :
    [lgtm| (new Point{x = 1, y = 2}).x] =
      Expression.structGet (.structNew "Point" [("x", .intLit 1), ("y", .intLit 2)]) "x" :=
  rfl

example : [lgtm| (var"my-struct").x] = Expression.structGet (.varRef "my-struct") "x" :=
  rfl

-- A field read is tighter than arithmetic, and a struct is an ordinary operand everywhere else.
example : [lgtm| p.x + 1] = Expression.plus (.structGet (.varRef "p") "x") (.intLit 1) :=
  rfl

example : [lgtm| p :: ps] = Expression.lcons (.varRef "p") (.varRef "ps") :=
  rfl

example :
    [lgtm| g(p.x, p.y)] =
      Expression.app (.varRef "g") [.structGet (.varRef "p") "x", .structGet (.varRef "p") "y"] :=
  rfl

-- An update names only the fields it changes, in any order, and chains.
example : [lgtm| {p with x = 1}] = Expression.structUpdate (.varRef "p") [("x", .intLit 1)] :=
  rfl

example :
    [lgtm| {p with y = 2, x = 1}] =
      Expression.structUpdate (.varRef "p") [("y", .intLit 2), ("x", .intLit 1)] :=
  rfl

example :
    [lgtm| {{p with x = 1} with y = 2}] =
      Expression.structUpdate (.structUpdate (.varRef "p") [("x", .intLit 1)]) [("y", .intLit 2)] :=
  rfl

example :
    [lgtm| {p with x = p.x + 1}] =
      Expression.structUpdate (.varRef "p")
        [("x", .plus (.structGet (.varRef "p") "x") (.intLit 1))] :=
  rfl

/-- A point in the plane. -/
@[lgtm] structure Point where
  x : int
  y : int

-- The command builds the `StructDecl` field by field, in the order the fields are written.
example : Point = { name := "Point", fields := [("x", .int), ("y", .int)] } :=
  rfl

-- With no `as`, the IR name is the Lean name; `as` overrides it, as it does for `@[lgtm] def`.
@[lgtm] structure Renamed as"my-struct" where
  f : list int

example : Renamed.name = "my-struct" :=
  rfl

example : Renamed.fields = [("f", .list .int)] :=
  rfl

-- A struct may have no fields, and its fields may be of any type — another struct included.
@[lgtm] structure Nothing where

example : Nothing.fields = [] :=
  rfl

@[lgtm] private structure Box where
  label : string
  origin : struct Point
  step : (int) -> int

example :
    Box.fields = [("label", .string), ("origin", .struct "Point"), ("step", .fn [.int] .int)] :=
  rfl

-- A field name may not be written twice: the second is one no read could reach, so the command
-- says so where the name is rather than leaving `Program.check` to turn the declaration down.
/-- error: duplicate field `x`: a declaration names each field once -/
#guard_msgs in
@[lgtm] structure TwoXs where
  x : int
  x : string

-- Two structs may of course each have an `x`: a field name is scoped to the struct that declares
-- it, so the condition is on one declaration and never across them.
@[lgtm] private structure OtherX where
  x : string

example : OtherX.fields = [("x", .string)] :=
  rfl

/-- `fun (p : Point) => new Point { x = p.y, y = p.x }` -/
@[lgtm] def swap(p : struct Point) : struct Point := new Point{x = p.y, y = p.x}

-- And what the two commands build together type checks, which is the point of writing it this way.
#guard (swap.check { ss := Structs.ofDecls [Point] } []).isOk

#guard !(swap.check {} []).isOk

@[lgtm] def shift(p : struct Point)(d : int) : struct Point := {p with x = p.x + d}

#guard (shift.check { ss := Structs.ofDecls [Point] } []).isOk

/-- Whether two points are the same point, which is field for field. -/
@[lgtm] def samePoint as"same-point"(p : struct Point)(q : struct Point) : bool := p == q

#guard (samePoint.check { ss := Structs.ofDecls [Point] } []).isOk

#guard !(samePoint.check {} []).isOk

/-- The same comparison on `Box`es, which carry a `step` of function type. -/
private def sameBox : FuncDecl :=
  { samePoint with parameters := [("p", .struct "Box"), ("q", .struct "Box")] }

-- A struct is comparable when everything it carries is, so a `Box` is not — however ordinary its
-- other two fields are, and although every struct form other than `==` still works on one.
#guard !(sameBox.check { ss := Structs.ofDecls [Point, Box] } []).isOk

/-! ### Inductive types -/

-- An inductive type is written with its name, and is a type like any other.
example : [lgtm_ty| inductive Color] = Ty.ind "Color" :=
  rfl

example : [lgtm_ty| inductive "my-type"] = Ty.ind "my-type" :=
  rfl

example : [lgtm_ty| list inductive Color] = Ty.list (.ind "Color") :=
  rfl

example : [lgtm_ty| (inductive Color) -> struct Point] = Ty.fn [.ind "Color"] (.struct "Point") :=
  rfl

-- `new Type.Ctor(...)` applies a constructor, with the parentheses written even when it takes
-- nothing, the way a call of no arguments is.
example : [lgtm| new Color.Red()] = Expression.indNew "Color" "Red" [] :=
  rfl

example :
    [lgtm| new Color.Rgb(1, 2, 3)] =
      Expression.indNew "Color" "Rgb" [.intLit 1, .intLit 2, .intLit 3] :=
  rfl

example :
    [lgtm| new Shape.Rect(w + 1, f(2))] =
      Expression.indNew "Shape" "Rect"
        [.plus (.varRef "w") (.intLit 1), .app (.varRef "f") [.intLit 2]] :=
  rfl

example : [lgtm| new"my-type""my-ctor"(n)] = Expression.indNew "my-type" "my-ctor" [.varRef "n"] :=
  rfl

-- And it is an ordinary operand everywhere else, constructors nested inside it included.
example :
    [lgtm| new Color.Red() :: cs] = Expression.lcons (.indNew "Color" "Red" []) (.varRef "cs") :=
  rfl

example :
    [lgtm| new Tree.Node(new Tree.Leaf(), new Tree.Leaf())] =
      Expression.indNew "Tree" "Node" [.indNew "Tree" "Leaf" [], .indNew "Tree" "Leaf" []] :=
  rfl

-- A `match` is one alternative per constructor, each binding a name to everything that constructor
-- carries.
example :
    [lgtm| match c with | Red => 0 | Rgb(r, g, b) => r] =
      Expression.indMatch (.varRef "c")
        [("Red", [], .intLit 0), ("Rgb", ["r", "g", "b"], .varRef "r")] :=
  rfl

example :
    [lgtm| match f(1) with | Circle(r) => r] =
      Expression.indMatch (.app (.varRef "f") [.intLit 1]) [("Circle", ["r"], .varRef "r")] :=
  rfl

-- An alternative's expression extends as far right as it can, so it stops only at the next `|`, and
-- a `match` inside one needs parentheses just as a `let` does.
example :
    [lgtm| match c with | Red => 1 + 2 | Green => let x := 1; x + x] =
      Expression.indMatch (.varRef "c")
        [("Red", [], .plus (.intLit 1) (.intLit 2)),
          ("Green", [], .let_ "x" (.intLit 1) (.plus (.varRef "x") (.varRef "x")))] :=
  rfl

example :
    [lgtm| (match c with | Red => 1) + 2] =
      Expression.plus (.indMatch (.varRef "c") [("Red", [], .intLit 1)]) (.intLit 2) :=
  rfl

-- The parser is not the exhaustiveness check: a match with no alternatives at all is written the
-- same way as any other, and it is the type checker that has nothing to say for it.
example : [lgtm| match c with] = Expression.indMatch (.varRef "c") [] :=
  rfl

/-- A colour. -/
@[lgtm] inductive Color where
  | Red
  | Green
  | Blue

-- The command builds the `InductiveDecl` constructor by constructor, in the order they are written,
-- with an empty list of data types for the ones that carry nothing.
example : Color = { name := "Color", constructors := [("Red", []), ("Green", []), ("Blue", [])] } :=
  rfl

@[lgtm] inductive Shape where
  | Circle(int)
  | Rect(int, int)

example : Shape.constructors = [("Circle", [.int]), ("Rect", [.int, .int])] :=
  rfl

-- A constructor's data may be of any type, another inductive type and the type being declared
-- included: nothing about a constructor's types is resolved when it is declared.
@[lgtm] inductive Tree where
  | Leaf
  | Node(inductive Tree, inductive Tree)

example : Tree.constructors = [("Leaf", []), ("Node", [.ind "Tree", .ind "Tree"])] :=
  rfl

@[lgtm] inductive Wrapped where
  | C(list int, struct Point, (int) -> int)

example : Wrapped.constructors = [("C", [.list .int, .struct "Point", .fn [.int] .int])] :=
  rfl

-- With no `as`, the IR name is the Lean name; `as` overrides it, and a type may declare no
-- constructors at all — nothing can build a value of it, and nothing can take one apart.
@[lgtm] inductive RenamedInd as"my-type" where
  | C

example : RenamedInd.name = "my-type" :=
  rfl

@[lgtm] private inductive NoCtors where

example : NoCtors.constructors = [] :=
  rfl

-- A constructor name may not be written twice, for the reason a field name may not: the second is
-- one nothing could build and no alternative of a match could be checked against.
/-- error: duplicate constructor `Red`: a declaration names each constructor once -/
#guard_msgs in
@[lgtm] inductive TwoReds where
  | Red
  | Green
  | Red(int)

-- Two types may each have a `Red` all the same: a constructor name is scoped to the type that
-- declares it, which is why `new` and `Value.ind` both name the type as well.
@[lgtm] private inductive Hue where
  | Red
  | Green

example : Hue.constructors = [("Red", []), ("Green", [])] :=
  rfl

/-- The perimeter of `s`, which is what a `match` is for: one answer per constructor, computed from
what that constructor carries. -/
@[lgtm] def perimeter(s : inductive Shape) : int :=
  match s with | Circle(r) => r + r + r + r + r + r | Rect(w, h) => w + w + h + h

-- And what the two commands build together type checks, which is the point of writing it this way.
#guard (perimeter.check { is := Inductives.ofDecls [Shape] } []).isOk

#guard !(perimeter.check {} []).isOk

/-- `Rect` with both sides `n`, which is the other half: a constructor applied to values. -/
@[lgtm] def square(n : int) : inductive Shape := new Shape.Rect(n, n)

#guard (square.check { is := Inductives.ofDecls [Shape] } []).isOk

/-- Whether two trees are the same tree: the same constructors all the way down, carrying the same
data.  A type being recursive is no obstacle to comparing two values of it — each value is finite —
which is what makes this check. -/
@[lgtm] def sameTree as"same-tree"(a : inductive Tree)(b : inductive Tree) : bool := a == b

#guard (sameTree.check { is := Inductives.ofDecls [Tree] } []).isOk

#guard !(sameTree.check {} []).isOk

/-- The same comparison on `Wrapped`, whose one constructor carries a function among its data. -/
private def sameWrapped : FuncDecl :=
  { sameTree with parameters := [("a", .ind "Wrapped"), ("b", .ind "Wrapped")] }

#guard
  !(sameWrapped.check { ss := Structs.ofDecls [Point], is := Inductives.ofDecls [Wrapped] } []).isOk

/-! ### Options -/

-- An option type holds another type, which it carries rather than names, so it nests both ways and
-- needs no declaration to be written.
example : [lgtm_ty| option int] = Ty.option .int :=
  rfl

example : [lgtm_ty| option option int] = Ty.option (.option .int) :=
  rfl

example : [lgtm_ty| option list int] = Ty.option (.list .int) :=
  rfl

example : [lgtm_ty| list option int] = Ty.list (.option .int) :=
  rfl

example : [lgtm_ty| option struct Point] = Ty.option (.struct "Point") :=
  rfl

example : [lgtm_ty| option((int) -> int)] = Ty.option (.fn [.int] .int) :=
  rfl

example : [lgtm_ty| (option int) -> option string] = Ty.fn [.option .int] (.option .string) :=
  rfl

-- The option holding a value takes no annotation, and the empty one takes the type it is empty at.
example : [lgtm| some(1)] = Expression.optionSome (.intLit 1) :=
  rfl

example : [lgtm| some(x + 1)] = Expression.optionSome (.plus (.varRef "x") (.intLit 1)) :=
  rfl

example : [lgtm| some(some(1))] = Expression.optionSome (.optionSome (.intLit 1)) :=
  rfl

example : [lgtm| none : int] = Expression.optionNone .int :=
  rfl

example : [lgtm| none : list string] = Expression.optionNone (.list .string) :=
  rfl

example : [lgtm| none : option int] = Expression.optionNone (.option .int) :=
  rfl

example : [lgtm| none : ((int) -> int)] = Expression.optionNone (.fn [.int] .int) :=
  rfl

example : [lgtm| some(none : int)] = Expression.optionSome (.optionNone .int) :=
  rfl

-- The bare form above is what the grammar accepts, but Lean has no bare `e : T` term, so DSL code
-- writes the parenthesized spelling instead; it is the existing `(e)` form, and elaborates the same.
example : [lgtm| (none : int)] = Expression.optionNone .int :=
  rfl

example : [lgtm| (none : list (struct Point))] = Expression.optionNone (.list (.struct "Point")) :=
  rfl

-- `some` and `none` are keywords, so neither is a variable name inside a DSL term; outside one they
-- are Lean's own, which declaring them with `&` is what preserves.
example : [lgtm| var"some"] = Expression.varRef "some" :=
  rfl

example : [lgtm| var"none"] = Expression.varRef "none" :=
  rfl

example : (some 1 : Option Nat) = Option.some 1 :=
  rfl

example : (none : Option Nat) = Option.none :=
  rfl

-- Both are ordinary operands: the annotation stops at the type, so a `+` or a `==` after one
-- applies to the whole of it, and neither form needs parentheses to be an argument.
example :
    [lgtm| some(1) == none : int] =
      Expression.equals (.optionSome (.intLit 1)) (.optionNone .int) :=
  rfl

example :
    [lgtm| f(some(1), none : int)] =
      Expression.app (.varRef "f") [.optionSome (.intLit 1), .optionNone .int] :=
  rfl

example : [lgtm| some(1) :: os] = Expression.lcons (.optionSome (.intLit 1)) (.varRef "os") :=
  rfl

example :
    [lgtm| let o := some(1); o] = Expression.let_ "o" (.optionSome (.intLit 1)) (.varRef "o") :=
  rfl

example :
    [lgtm| if b then (some(1)) else (none : int)] =
      Expression.ite (.varRef "b") (.optionSome (.intLit 1)) (.optionNone .int) :=
  rfl

example : [lgtm| fun(o : option int) => o] = Expression.lam [("o", .option .int)] (.varRef "o") :=
  rfl

-- A list literal ends with an annotation of its own, so an empty option inside one is parenthesized
-- to say which `:` is which.
example :
    [lgtm| [(none : int) : option int]] =
      Expression.lcons (.optionNone .int) (.lnil (.option .int)) :=
  rfl

example :
    [lgtm| [some(1), (none : int) : option int]] =
      Expression.lcons (.optionSome (.intLit 1))
        (.lcons (.optionNone .int) (.lnil (.option .int))) :=
  rfl

-- A `match` on an option is the two cases it has, which is an `optionMatch` rather than an
-- `indMatch`: the empty case computes with nothing and the other binds what the option held.
example :
    [lgtm| match o with | none => 0 | some(x) => x + 1] =
      Expression.optionMatch (.varRef "o") (.intLit 0) "x" (.plus (.varRef "x") (.intLit 1)) :=
  rfl

example :
    [lgtm| match f(1) with | none => "" | some(s) => s] =
      Expression.optionMatch (.app (.varRef "f") [.intLit 1]) (.stringLit "") "s" (.varRef "s") :=
  rfl

example :
    [lgtm| match some(1) with | none => 0 | some(x) => x] =
      Expression.optionMatch (.optionSome (.intLit 1)) (.intLit 0) "x" (.varRef "x") :=
  rfl

-- An alternative's expression extends as far right as it can here too, so a match nested in one
-- needs no parentheses and one nested in the scrutinee does.
example :
    [lgtm| match o with | none => 0 | some(x) => match x with | none => 1 | some(y) => y] =
      Expression.optionMatch (.varRef "o") (.intLit 0) "x"
        (.optionMatch (.varRef "x") (.intLit 1) "y" (.varRef "y")) :=
  rfl

example :
    [lgtm| (match o with | none => 0 | some(x) => x) + 1] =
      Expression.plus (.optionMatch (.varRef "o") (.intLit 0) "x" (.varRef "x")) (.intLit 1) :=
  rfl

-- A match naming neither is the `indMatch` it was, which is what the special case is special to.
example :
    [lgtm| match c with | Red => 0 | Rgb(r, g, b) => r] =
      Expression.indMatch (.varRef "c")
        [("Red", [], .intLit 0), ("Rgb", ["r", "g", "b"], .varRef "r")] :=
  rfl

-- The heads `none` and `some` are keywords, but only exactly: a constructor whose name begins with
-- one of them is the identifier it looks like, and the alternative an `indMatch`'s.
example :
    [lgtm| match c with | noneOfThese => 0 | someThing(y) => y] =
      Expression.indMatch (.varRef "c")
        [("noneOfThese", [], .intLit 0), ("someThing", ["y"], .varRef "y")] :=
  rfl

/-- One more than what `o` holds, and zero when it holds nothing: the two option forms and the match
between them, which is what a declaration returning an `int` from an option looks like. -/
@[lgtm] def succOrZero as"succ-or-zero"(o : option int) : int :=
  match o with | none => 0 | some(x) => x + 1

-- An option needs no declaration to be well formed, so this checks against no `TypeDecls` at all.
#guard (succOrZero.check {} []).isOk

-- The two cases have to share a type, and the name bound is the type the option holds — so `x + 1`
-- is an `int` because the parameter is an `option int`.
#guard
  !(({ succOrZero with body := [lgtm| match o with | none => 0 | some(x) => "a"] } : FuncDecl).check
        {} []).isOk

#guard
  !(({ succOrZero with parameters := [("o", [lgtm_ty| option string])] } : FuncDecl).check {}
        []).isOk

-- And the scrutinee has to be an option: a list is not one, however much the match looks like it
-- could take one apart.
#guard
  !(({ succOrZero with parameters := [("o", [lgtm_ty| list int])] } : FuncDecl).check {} []).isOk

/-- `n`, held in an option, which is the other half: a value put into one rather than taken out. -/
@[lgtm] def justInt as"just-int"(n : int) : option int := some(n)

#guard (justInt.check {} []).isOk

#guard !(({ justInt with resultType := [lgtm_ty| option string] } : FuncDecl).check {} []).isOk

/-- Nothing, at `int`: the shortest declaration returning an option, and the one place the
annotation is all there is to go on. -/
@[lgtm] def noInt as"no-int" : option int := none : int

#guard (noInt.check {} []).isOk

#guard !(({ noInt with resultType := [lgtm_ty| option string] } : FuncDecl).check {} []).isOk

/-- Whether two options are the same option, which an option is as comparable as what it holds. -/
@[lgtm] def sameOpt as"same-opt"(a : option int)(b : option int) : bool := a == b

#guard (sameOpt.check {} []).isOk

-- So an option of function type is no more comparable than the functions it holds.
#guard
  !(({ sameOpt with parameters := [("a", .option fnTy), ("b", .option fnTy)] } : FuncDecl).check {}
        []).isOk

-- Both alternatives are required and in the order `optionMatch` holds them, since there is nothing
-- else a `match` naming `none` could have meant.
/-- error: a match on an option takes `none` first and `some` second -/
#guard_msgs (error) in
#check [lgtm| match o with | some(x) => x | none => 0]

/-- error: a match on an option has two alternatives: `| none => ... | some(x) => ...` -/
#guard_msgs (error) in
#check [lgtm| match o with | none => 0]

/-- error: `some` holds one value, so its alternative binds one name: `| some(x) => ...` -/
#guard_msgs (error) in
#check [lgtm| match o with | none => 0 | some(x, y) => x]

/-- error: `none` holds nothing, so its alternative binds no names -/
#guard_msgs (error) in
#check [lgtm| match o with | none(x) => 0 | some(y) => y]

/-! ### Excepts -/

-- An except type is written with the two types it relates, the error first, and is a type like any
-- other: it nests both ways and needs no declaration to be written.
example : [lgtm_ty| except string int] = Ty.except .string .int :=
  rfl

example : [lgtm_ty| except int string] = Ty.except .int .string :=
  rfl

example : [lgtm_ty| except string list int] = Ty.except .string (.list .int) :=
  rfl

example : [lgtm_ty| except list string int] = Ty.except (.list .string) .int :=
  rfl

example : [lgtm_ty| except string except string int] = Ty.except .string (.except .string .int) :=
  rfl

example : [lgtm_ty| option except string int] = Ty.option (.except .string .int) :=
  rfl

example : [lgtm_ty| except string struct Point] = Ty.except .string (.struct "Point") :=
  rfl

example : [lgtm_ty| except string((int) -> int)] = Ty.except .string (.fn [.int] .int) :=
  rfl

example : [lgtm_ty| (except string int) -> int] = Ty.fn [.except .string .int] .int :=
  rfl

-- Both values carry a type, and in both it is the half the value itself does not say: a success
-- says the payload type, so its annotation is the error type, and a failure the other way round.
example : [lgtm| ok(1) : string] = Expression.exceptOk .string (.intLit 1) :=
  rfl

example : [lgtm| error("no") : int] = Expression.exceptError .int (.stringLit "no") :=
  rfl

example :
    [lgtm| ok(x + 1) : string] =
      Expression.exceptOk .string (.plus (.varRef "x") (.intLit 1)) :=
  rfl

example : [lgtm| ok(1) : list string] = Expression.exceptOk (.list .string) (.intLit 1) :=
  rfl

example : [lgtm| ok(1) : ((int) -> int)] = Expression.exceptOk (.fn [.int] .int) (.intLit 1) :=
  rfl

example :
    [lgtm| ok(ok(1) : string) : string] =
      Expression.exceptOk .string (.exceptOk .string (.intLit 1)) :=
  rfl

-- The bare form above is what the grammar accepts, but DSL code writes the parenthesized spelling
-- for the reason it writes `(none : T)`; it is the existing `(e)` form, and elaborates the same.
example : [lgtm| (ok(1) : string)] = Expression.exceptOk .string (.intLit 1) :=
  rfl

example : [lgtm| (error("no") : int)] = Expression.exceptError .int (.stringLit "no") :=
  rfl

-- `ok` and `error` are keywords, so neither is a variable name inside a DSL term; outside one they
-- are Lean's own, which declaring them with `&` is what preserves.
example : [lgtm| var"ok"] = Expression.varRef "ok" :=
  rfl

example : [lgtm| var"error"] = Expression.varRef "error" :=
  rfl

example : (Except.ok 1 : Except String Nat) = .ok 1 :=
  rfl

-- Both are ordinary operands: the annotation stops at the type, so a `==` after one applies to the
-- whole of it, and neither form needs parentheses to be an argument.
example :
    [lgtm| ok(1) : string == error("no") : int] =
      Expression.equals (.exceptOk .string (.intLit 1)) (.exceptError .int (.stringLit "no")) :=
  rfl

example :
    [lgtm| f(ok(1) : string, error("no") : int)] =
      Expression.app (.varRef "f")
        [.exceptOk .string (.intLit 1), .exceptError .int (.stringLit "no")] :=
  rfl

example :
    [lgtm| if b then (ok(1) : string) else (error("no") : int)] =
      Expression.ite (.varRef "b") (.exceptOk .string (.intLit 1))
        (.exceptError .int (.stringLit "no")) :=
  rfl

example :
    [lgtm| fun(r : except string int) => r] =
      Expression.lam [("r", .except .string .int)] (.varRef "r") :=
  rfl

-- A list literal ends with an annotation of its own, so an except inside one is parenthesized to
-- say which `:` is which.
example :
    [lgtm| [(ok(1) : string) : except string int]] =
      Expression.lcons (.exceptOk .string (.intLit 1)) (.lnil (.except .string .int)) :=
  rfl

-- A `match` on an except is the two cases it has, which is an `exceptMatch` rather than an
-- `indMatch`: each case binds what its half of the value carried.
example :
    [lgtm| match r with | error(e) => 0 | ok(x) => x + 1] =
      Expression.exceptMatch (.varRef "r") "e" (.intLit 0) "x"
        (.plus (.varRef "x") (.intLit 1)) :=
  rfl

example :
    [lgtm| match f(1) with | error(m) => m | ok(s) => s] =
      Expression.exceptMatch (.app (.varRef "f") [.intLit 1]) "m" (.varRef "m") "s"
        (.varRef "s") :=
  rfl

-- An alternative's expression extends as far right as it can here too, so a match nested in one
-- needs no parentheses and one nested in the scrutinee does.
example :
    [lgtm| match r with | error(e) => 0 | ok(x) => match x with | error(e2) => 1 | ok(y) => y] =
      Expression.exceptMatch (.varRef "r") "e" (.intLit 0) "x"
        (.exceptMatch (.varRef "x") "e2" (.intLit 1) "y" (.varRef "y")) :=
  rfl

example :
    [lgtm| (match r with | error(e) => 0 | ok(x) => x) + 1] =
      Expression.plus (.exceptMatch (.varRef "r") "e" (.intLit 0) "x" (.varRef "x")) (.intLit 1) :=
  rfl

-- The heads `error` and `ok` are keywords, but only exactly: a constructor whose name begins with
-- one of them is the identifier it looks like, and the alternative an `indMatch`'s.
example :
    [lgtm| match c with | errorish => 0 | okish(y) => y] =
      Expression.indMatch (.varRef "c")
        [("errorish", [], .intLit 0), ("okish", ["y"], .varRef "y")] :=
  rfl

/-- What `r` holds, and zero when it failed: the two except forms and the match between them, which
is what a declaration returning an `int` from an except looks like. -/
@[lgtm] def intOrZero as"int-or-zero"(r : except string int) : int :=
  match r with | error(e) => 0 | ok(x) => x

-- An except needs no declaration to be well formed, so this checks against no `TypeDecls` at all.
#guard (intOrZero.check {} []).isOk

-- The two cases have to share a type, and each name is bound at its half of the scrutinee's type —
-- so `x` is an `int` and `e` a `string` because the parameter is an `except string int`.
#guard
  !(({ intOrZero with body := [lgtm| match r with | error(e) => 0 | ok(x) => "a"] } :
        FuncDecl).check {} []).isOk

#guard
  !(({ intOrZero with body := [lgtm| match r with | error(e) => e | ok(x) => x] } :
        FuncDecl).check {} []).isOk

#guard
  !(({ intOrZero with parameters := [("r", [lgtm_ty| except string string])] } : FuncDecl).check {}
        []).isOk

-- And the scrutinee has to be an except: an option is not one, however much the match looks like it
-- could take one apart.
#guard
  !(({ intOrZero with parameters := [("r", [lgtm_ty| option int])] } : FuncDecl).check {} []).isOk

/-- `n`, held in a successful except, which is the other half: a value put into one rather than
taken out.  The annotation is the error type, which nothing here carries a value of. -/
@[lgtm] def okInt as"ok-int"(n : int) : except string int := ok(n) : string

#guard (okInt.check {} []).isOk

#guard !(({ okInt with resultType := [lgtm_ty| except int int] } : FuncDecl).check {} []).isOk

/-- A failure at `except string int`, where the annotation is the payload type instead. -/
@[lgtm] def failInt as"fail-int"(m : string) : except string int := error(m) : int

#guard (failInt.check {} []).isOk

#guard !(({ failInt with resultType := [lgtm_ty| except string string] } : FuncDecl).check {}
    []).isOk

/-- Whether two excepts are the same, which an except is as comparable as both of its halves. -/
@[lgtm] def sameExcept as"same-except"(a : except string int)(b : except string int) : bool :=
  a == b

#guard (sameExcept.check {} []).isOk

-- So an except of function type on either half is no more comparable than the functions it holds.
#guard
  !(({ sameExcept with
        parameters := [("a", .except fnTy .int), ("b", .except fnTy .int)] } : FuncDecl).check {}
        []).isOk

#guard
  !(({ sameExcept with
        parameters := [("a", .except .string fnTy), ("b", .except .string fnTy)] } :
      FuncDecl).check {} []).isOk

-- And an except has no ordering, where an option of the same types has one: an error and a success
-- carry values of two unrelated types, so neither comes first.
#guard
  !(({ sameExcept with body := [lgtm| a <= b] } : FuncDecl).check {} []).isOk

-- Both alternatives are required and in the order `exceptMatch` holds them, since there is nothing
-- else a `match` naming `error` could have meant.
/-- error: a match on an except takes `error` first and `ok` second -/
#guard_msgs (error) in
#check [lgtm| match r with | ok(x) => x | error(e) => 0]

/-- error: a match on an except has two alternatives: `| error(e) => ... | ok(x) => ...` -/
#guard_msgs (error) in
#check [lgtm| match r with | error(e) => 0]

/-- error: `ok` holds one value, so its alternative binds one name: `| ok(x) => ...` -/
#guard_msgs (error) in
#check [lgtm| match r with | error(e) => 0 | ok(x, y) => x]

/-- error: `error` holds one value, so its alternative binds one name: `| error(e) => ...` -/
#guard_msgs (error) in
#check [lgtm| match r with | error() => 0 | ok(y) => y]

/-! ### Hashmaps -/

-- A hashmap type is written with the two types it relates, in that order, and is a type like any
-- other: it nests both ways and needs no declaration to be written.
example : [lgtm_ty| hashmap string int] = Ty.hashmap .string .int :=
  rfl

example : [lgtm_ty| hashmap int string] = Ty.hashmap .int .string :=
  rfl

example : [lgtm_ty| hashmap string list int] = Ty.hashmap .string (.list .int) :=
  rfl

example : [lgtm_ty| hashmap list string int] = Ty.hashmap (.list .string) .int :=
  rfl

example : [lgtm_ty| hashmap string option int] = Ty.hashmap .string (.option .int) :=
  rfl

example : [lgtm_ty| hashmap string struct Point] = Ty.hashmap .string (.struct "Point") :=
  rfl

example : [lgtm_ty| hashmap string((int) -> int)] = Ty.hashmap .string (.fn [.int] .int) :=
  rfl

example :
    [lgtm_ty| hashmap string hashmap string int] = Ty.hashmap .string (.hashmap .string .int) :=
  rfl

example : [lgtm_ty| list hashmap string int] = Ty.list (.hashmap .string .int) :=
  rfl

example : [lgtm_ty| option hashmap string int] = Ty.option (.hashmap .string .int) :=
  rfl

example : [lgtm_ty| (hashmap string int) -> int] = Ty.fn [.hashmap .string .int] .int :=
  rfl

-- The empty map carries both of its types, for the reason an empty list carries its one: it binds
-- nothing, so there is neither a key nor a value to read either off.
example : [lgtm| hashmap(string, int)] = Expression.hashmapEmpty .string .int :=
  rfl

example : [lgtm| hashmap(int, list string)] = Expression.hashmapEmpty .int (.list .string) :=
  rfl

example :
    [lgtm| hashmap(string, hashmap string int)] =
      Expression.hashmapEmpty .string (.hashmap .string .int) :=
  rfl

example :
    [lgtm| hashmap(string, (int) -> int)] = Expression.hashmapEmpty .string (.fn [.int] .int) :=
  rfl

-- `hashmap` is a keyword, so it is no variable name inside a DSL term; outside one it is an
-- ordinary Lean identifier, which declaring it with `&` is what preserves.
example : [lgtm| var"hashmap"] = Expression.varRef "hashmap" :=
  rfl

-- A lookup is written with no space before the `[`, which is what tells it from a list literal.
example : [lgtm| m[k]] = Expression.hashmapGet (.varRef "m") (.varRef "k") :=
  rfl

example : [lgtm| m["a"]] = Expression.hashmapGet (.varRef "m") (.stringLit "a") :=
  rfl

example :
    [lgtm| m[x + 1]] = Expression.hashmapGet (.varRef "m") (.plus (.varRef "x") (.intLit 1)) :=
  rfl

-- It binds as tightly as a field read does, and nests into itself and into the other postfix forms.
example :
    [lgtm| m[a][b]] =
      Expression.hashmapGet (.hashmapGet (.varRef "m") (.varRef "a")) (.varRef "b") :=
  rfl

example : [lgtm| p.m[k]] = Expression.hashmapGet (.structGet (.varRef "p") "m") (.varRef "k") :=
  rfl

example : [lgtm| f(1)[k]] = Expression.hashmapGet (.app (.varRef "f") [.intLit 1]) (.varRef "k") :=
  rfl

-- And what it produces is an ordinary operand: an option, so a comparison and a match both read one
-- with no parentheses.
example :
    [lgtm| m[k] + 1] = Expression.plus (.hashmapGet (.varRef "m") (.varRef "k")) (.intLit 1) :=
  rfl

example :
    [lgtm| m[k] == none : int] =
      Expression.equals (.hashmapGet (.varRef "m") (.varRef "k")) (.optionNone .int) :=
  rfl

example :
    [lgtm| match m[k] with | none => 0 | some(x) => x] =
      Expression.optionMatch (.hashmapGet (.varRef "m") (.varRef "k")) (.intLit 0) "x"
        (.varRef "x") :=
  rfl

-- An update names its keys in brackets and is one `hashmapPut` apiece, applied left to right, so
-- writing two is the same as nesting two.
example :
    [lgtm| {m with [k] = 1}] = Expression.hashmapPut (.varRef "m") (.varRef "k") (.intLit 1) :=
  rfl

example :
    [lgtm| {m with ["a"] = 1, ["b"] = 2}] =
      Expression.hashmapPut (.hashmapPut (.varRef "m") (.stringLit "a") (.intLit 1))
        (.stringLit "b") (.intLit 2) :=
  rfl

example :
    [lgtm| {{m with ["a"] = 1} with ["b"] = 2}] =
      Expression.hashmapPut (.hashmapPut (.varRef "m") (.stringLit "a") (.intLit 1))
        (.stringLit "b") (.intLit 2) :=
  rfl

example :
    [lgtm| {hashmap(string, int) with ["a"] = 1}] =
      Expression.hashmapPut (.hashmapEmpty .string .int) (.stringLit "a") (.intLit 1) :=
  rfl

example :
    [lgtm| {m with [k] = x + 1}] =
      Expression.hashmapPut (.varRef "m") (.varRef "k") (.plus (.varRef "x") (.intLit 1)) :=
  rfl

-- The brackets are the whole of what tells a map update from a struct update — a field is a name
-- and a key is an expression — so the two forms never meet and `{ p with }` is the struct update it
-- has always been.
example : [lgtm| {p with x = 1}] = Expression.structUpdate (.varRef "p") [("x", .intLit 1)] :=
  rfl

example : [lgtm| {p with }] = Expression.structUpdate (.varRef "p") [] :=
  rfl

-- An update is an operand like any other, so a lookup reads one with no parentheses.
example :
    [lgtm| {m with ["a"] = 1}["a"]] =
      Expression.hashmapGet (.hashmapPut (.varRef "m") (.stringLit "a") (.intLit 1))
        (.stringLit "a") :=
  rfl

-- The brackets are one form over two readings, and the type inferred for what is indexed is what
-- says which: a list gives a `listIndex` and everything else a `hashmapGet`.  A list literal
-- carries its own element type, so it is a list even in a fragment, where nothing else is.
example :
    [lgtm| [1, 2 : int][0]] =
      Expression.listIndex (.lcons (.intLit 1) (.lcons (.intLit 2) (.lnil .int))) (.intLit 0) :=
  rfl

example : [lgtm| [ : int][0]] = Expression.listIndex (.lnil .int) (.intLit 0) :=
  rfl

example :
    [lgtm| [new Point{x = 1, y = 2} : struct Point][0]] =
      Expression.listIndex
        (.lcons (.structNew "Point" [("x", .intLit 1), ("y", .intLit 2)]) (.lnil (.struct "Point")))
        (.intLit 0) :=
  rfl

-- What was consulted is the operand's type rather than how it was arrived at, so anything else a
-- type is readable off reads the same way.
example :
    [lgtm| (reverse [1, 2 : int])[0]] =
      Expression.listIndex (.listReverse (.lcons (.intLit 1) (.lcons (.intLit 2) (.lnil .int))))
        (.intLit 0) :=
  rfl

example :
    [lgtm| (toList hashmap(string, int))[0]] =
      Expression.listIndex (.hashmapToList (.hashmapEmpty .string .int)) (.intLit 0) :=
  rfl

-- The index is itself a postfix form at `max`, which is where `reverse`'s operand is read, so an
-- unparenthesized `reverse` reads the brackets first and takes the index as its operand.
example :
    [lgtm| reverse [1, 2 : int][0]] =
      Expression.listReverse
        (.listIndex (.lcons (.intLit 1) (.lcons (.intLit 2) (.lnil .int))) (.intLit 0)) :=
  rfl

-- An operand whose type is a hashmap is the lookup it has always been.
example :
    [lgtm| hashmap(string, int)["a"]] =
      Expression.hashmapGet (.hashmapEmpty .string .int) (.stringLit "a") :=
  rfl

-- And so is one with no type at all, which is the documented fallback: a fragment has no context,
-- so a free name has nothing to be read by and the brackets stay the lookup every `m[k]` written
-- before an index existed was.  An index over a free name is written inside a declaration instead.
example : [lgtm| xs[0]] = Expression.hashmapGet (.varRef "xs") (.intLit 0) :=
  rfl

example : [lgtm| xs[i]] = Expression.hashmapGet (.varRef "xs") (.varRef "i") :=
  rfl

-- What an index produces is an ordinary operand, an option, so the forms that read one read it with
-- no parentheses — the same nesting a lookup has, over a literal here because a fragment is where
-- the ill-typed ones can be written at all.
example :
    [lgtm| [1 : int][0] + 1] =
      Expression.plus (.listIndex (.lcons (.intLit 1) (.lnil .int)) (.intLit 0)) (.intLit 1) :=
  rfl

example :
    [lgtm| [1 : int][0] == none : int] =
      Expression.equals (.listIndex (.lcons (.intLit 1) (.lnil .int)) (.intLit 0))
        (.optionNone .int) :=
  rfl

example :
    [lgtm| match [1 : int][0] with | none => 0 | some(x) => x] =
      Expression.optionMatch (.listIndex (.lcons (.intLit 1) (.lnil .int)) (.intLit 0)) (.intLit 0)
        "x" (.varRef "x") :=
  rfl

-- And the index itself is an expression like any other.
example :
    [lgtm| [1, 2 : int][i + 1]] =
      Expression.listIndex (.lcons (.intLit 1) (.lcons (.intLit 2) (.lnil .int)))
        (.plus (.varRef "i") (.intLit 1)) :=
  rfl

example :
    [lgtm| [1, 2 : int][length [1, 2 : int] - 1]] =
      Expression.listIndex (.lcons (.intLit 1) (.lcons (.intLit 2) (.lnil .int)))
        (.minus (.listLength (.lcons (.intLit 1) (.lcons (.intLit 2) (.lnil .int)))) (.intLit 1)) :=
  rfl

-- Chaining is where the two readings part company.  The first bracket of a `list list int` is an
-- index and hands back an `option list int`, and an option is no list, so the second is a lookup —
-- where `m[k1][k2]` is two lookups because neither needs the first to have produced a map.  See
-- `chkChainedIndex` below for what that costs inside a declaration.
example :
    [lgtm| [[1 : int] : list int][0][0]] =
      Expression.hashmapGet
        (.listIndex (.lcons (.lcons (.intLit 1) (.lnil .int)) (.lnil (.list .int))) (.intLit 0))
        (.intLit 0) :=
  rfl

/-- A struct with a list in it, to index a field read. -/
@[lgtm] structure Bag where
  items : list int

/-- The element of `xs` at `i`, and zero where there is none.  A parameter is where a declaration's
operands come from, and the type declared for it is what the brackets are read by — so this is the
shape real code writes an index in, where a fragment needs an operand carrying its own type. -/
@[lgtm] def elemOr as"elem-or"(xs : list int)(i : int) : int :=
  match xs[i] with | none => 0 | some(x) => x

#guard (elemOr.check {} []).isOk

example :
    elemOr.body =
      Expression.optionMatch (.listIndex (.varRef "xs") (.varRef "i")) (.intLit 0) "x"
        (.varRef "x") :=
  rfl

-- And what the brackets were read as is settled once, where the body was elaborated: changing the
-- parameter's type afterwards leaves the index where it is, now over a hashmap, which does not
-- check.
#guard
  !(({ elemOr with parameters := [("xs", [lgtm_ty| hashmap int int]), ("i", .int)] } :
            FuncDecl).check
        {} []).isOk

/-- The same declaration over a hashmap, which is the dispatch read the other way: the brackets are
the ones above, and the type of what is indexed is the whole of what tells the two apart. -/
@[lgtm] def valueOr as"value-or"(m : hashmap int int)(k : int) : int :=
  match m[k] with | none => 0 | some(x) => x

#guard (valueOr.check {} []).isOk

example :
    valueOr.body =
      Expression.optionMatch (.hashmapGet (.varRef "m") (.varRef "k")) (.intLit 0) "x"
        (.varRef "x") :=
  rfl

/-- The same read over a `let`, which is the other place a declaration's operands come from: the
type the name is bound at is what the brackets are read by, exactly as a parameter's is. -/
@[lgtm] def firstOrZero as"first-or-zero"(p : struct Point) : int :=
  let ys := [p.x, p.y : int];
  match ys[0] with | none => 0 | some(x) => x

#guard (firstOrZero.check { ss := Structs.ofDecls [Point] } []).isOk

example :
    firstOrZero.body =
      Expression.let_ "ys"
        (.lcons (.structGet (.varRef "p") "x") (.lcons (.structGet (.varRef "p") "y") (.lnil .int)))
        (.optionMatch (.listIndex (.varRef "ys") (.intLit 0)) (.intLit 0) "x" (.varRef "x")) :=
  rfl

/-- A field's list and a call's list are both indexed with no parentheses, the way a lookup reads
`p.m[k]` and `f(1)[k]`: the brackets bind as tightly as the field read and the call do. -/
@[lgtm] def bagAt as"bag-at"(b : struct Bag)(i : int) : option int :=
  b.items[i]

example : bagAt.body = Expression.listIndex (.structGet (.varRef "b") "items") (.varRef "i") :=
  rfl

@[lgtm] def bangAt as"bang-at"(s : string) : option string :=
  bang(s)[0]

example :
    bangAt.body = Expression.listIndex (.app (.varRef "bang") [.varRef "s"]) (.intLit 0) :=
  rfl

-- An index of a `list list int` does not chain: the first bracket hands back an `option list int`,
-- which is no list, so the second reads as a lookup and the declaration does not check.  That is
-- the whole of what the fallback costs inside a declaration, and it is reported on the chain rather
-- than anywhere else.
/-- error: `m[k]` needs a hashmap, but what is looked up in here has type option list int -/
#guard_msgs (error) in
@[lgtm] def chkChainedIndex(xss : list list int) : option int :=
  xss[0][0]

example :
    chkChainedIndex.body =
      Expression.hashmapGet (.listIndex (.varRef "xss") (.intLit 0)) (.intLit 0) :=
  rfl

-- A tuple type lists its types in one group in parentheses, the way a function type's parameters
-- are listed and unlike `hashmap`'s two: the group is what says how many there are, so a function
-- type among them needs no parentheses of its own and there is an empty one to write.
example : [lgtm_ty| tuple(string, int)] = Ty.tuple [.string, .int] :=
  rfl

example : [lgtm_ty| tuple(int, string)] = Ty.tuple [.int, .string] :=
  rfl

example : [lgtm_ty| tuple()] = Ty.tuple [] :=
  rfl

example : [lgtm_ty| tuple(int)] = Ty.tuple [.int] :=
  rfl

example : [lgtm_ty| tuple(int, string, bool)] = Ty.tuple [.int, .string, .bool] :=
  rfl

example : [lgtm_ty| tuple(list int, option string)] = Ty.tuple [.list .int, .option .string] :=
  rfl

example : [lgtm_ty| tuple(string, (int) -> int)] = Ty.tuple [.string, .fn [.int] .int] :=
  rfl

example : [lgtm_ty| tuple(string, tuple(int, bool))] = Ty.tuple [.string, .tuple [.int, .bool]] :=
  rfl

example : [lgtm_ty| list tuple(string, int)] = Ty.list (.tuple [.string, .int]) :=
  rfl

example : [lgtm_ty| hashmap tuple(string, int)int] = Ty.hashmap (.tuple [.string, .int]) .int :=
  rfl

-- A conversion is a prefix keyword binding as tightly as `reverse`, so it reads a lookup's operand
-- and takes parentheses to reach further.
example : [lgtm| toList m] = Expression.hashmapToList (.varRef "m") :=
  rfl

example : [lgtm| toList p.m] = Expression.hashmapToList (.structGet (.varRef "p") "m") :=
  rfl

example : [lgtm| toList f(1)] = Expression.hashmapToList (.app (.varRef "f") [.intLit 1]) :=
  rfl

example :
    [lgtm| toList hashmap(string, int)] = Expression.hashmapToList (.hashmapEmpty .string .int) :=
  rfl

example :
    [lgtm| toList({m with [k] = 1})] =
      Expression.hashmapToList (.hashmapPut (.varRef "m") (.varRef "k") (.intLit 1)) :=
  rfl

-- And what it produces is an ordinary list operand: `reverse` reads one, a cons extends one, and a
-- comparison against the empty list is what asking whether a map binds anything comes to.
example : [lgtm| reverse toList m] = Expression.listReverse (.hashmapToList (.varRef "m")) :=
  rfl

example :
    [lgtm| toList m == [ : tuple(string, int)]] =
      Expression.equals (.hashmapToList (.varRef "m")) (.lnil (.tuple [.string, .int])) :=
  rfl

-- `toList` is a keyword, so it is no variable name inside a DSL term; outside one it is an ordinary
-- Lean identifier, which declaring it with `&` is what preserves.
example : [lgtm| var"toList"] = Expression.varRef "toList" :=
  rfl

-- A mapping over a hashmap is a prefix keyword with two operands, both of them binding as tightly
-- as `toList`'s one, and it is the type of the first that says it is a hashmap's rather than a
-- list's — so a fragment writes one over an operand carrying its own type, the way an index is
-- written in one.
example :
    [lgtm| map hashmap(string, int)f] =
      Expression.hashmapMap (.hashmapEmpty .string .int) (.varRef "f") :=
  rfl

example :
    [lgtm| map ({hashmap(string, int) with ["a"] = 1})g(1)] =
      Expression.hashmapMap (.hashmapPut (.hashmapEmpty .string .int) (.stringLit "a") (.intLit 1))
        (.app (.varRef "g") [.intLit 1]) :=
  rfl

-- A function written out is the loosest form there is, so it takes the parentheses an operand at
-- that level needs — and the key comes before the value, which is the order the parameters go in.
example : [lgtm| map hashmap(string, int) (fun (k : string) (v : int) => v + 1)]
    = Expression.hashmapMap (.hashmapEmpty .string .int)
        (.lam [("k", .string), ("v", .int)] (.plus (.varRef "v") (.intLit 1))) := rfl

example : [lgtm| map hashmap(string, int) (fun (k : string) (v : int) => k)]
    = Expression.hashmapMap (.hashmapEmpty .string .int)
        (.lam [("k", .string), ("v", .int)] (.varRef "k")) := rfl

-- What it produces is a map, so every form that reads one reads this: a lookup, an update, another
-- mapping, and a conversion.  The lookup and the second mapping are read by the type of what they
-- are given, which is where the function has to be written out for the mapping to have one.
example :
    [lgtm| (map hashmap(string, int)f)[k]] =
      Expression.hashmapGet (.hashmapMap (.hashmapEmpty .string .int) (.varRef "f")) (.varRef "k") :=
  rfl

example :
    [lgtm| {map hashmap(string, int)f with [k] = 1}] =
      Expression.hashmapPut (.hashmapMap (.hashmapEmpty .string .int) (.varRef "f")) (.varRef "k")
        (.intLit 1) :=
  rfl

example :
    [lgtm| map (map hashmap(string, int) (fun (k : string) (v : int) => v))g] =
      Expression.hashmapMap
        (.hashmapMap (.hashmapEmpty .string .int) (.lam [("k", .string), ("v", .int)] (.varRef "v")))
        (.varRef "g") :=
  rfl

example :
    [lgtm| toList(map hashmap(string, int)f)] =
      Expression.hashmapToList (.hashmapMap (.hashmapEmpty .string .int) (.varRef "f")) :=
  rfl

-- The same keyword over the other thing there is to map over reads its two operands the same way,
-- and is what everything a hashmap type is not deduced for reads as — a name, a field read and a
-- call among them, since a fragment gives none of them a type.
example : [lgtm| map xs f] = Expression.listMap (.varRef "xs") (.varRef "f") :=
  rfl

example :
    [lgtm| map p.items f] =
      Expression.listMap (.structGet (.varRef "p") "items") (.varRef "f") :=
  rfl

example :
    [lgtm| map g(1)f] = Expression.listMap (.app (.varRef "g") [.intLit 1]) (.varRef "f") :=
  rfl

example :
    [lgtm| map[1, 2 : int]f] =
      Expression.listMap (.lcons (.intLit 1) (.lcons (.intLit 2) (.lnil .int))) (.varRef "f") :=
  rfl

example : [lgtm| map[ : int]f] = Expression.listMap (.lnil .int) (.varRef "f") :=
  rfl

-- Its function takes one parameter where a hashmap's takes two, which is the one thing written out
-- that says which mapping was meant: an element is one value where a binding is a key beside its
-- value.
example : [lgtm| map xs (fun (x : int) => x + 1)]
    = Expression.listMap (.varRef "xs") (.lam [("x", .int)] (.plus (.varRef "x") (.intLit 1)))
    := rfl

-- What it produces is a list, so every form that reads one reads this: a reversal, a length, a cons,
-- and another mapping.
example :
    [lgtm| reverse(map xs f)] =
      Expression.listReverse (.listMap (.varRef "xs") (.varRef "f")) :=
  rfl

example :
    [lgtm| length(map xs f)] = Expression.listLength (.listMap (.varRef "xs") (.varRef "f")) :=
  rfl

example :
    [lgtm| x :: map xs f] =
      Expression.lcons (.varRef "x") (.listMap (.varRef "xs") (.varRef "f")) :=
  rfl

example :
    [lgtm| map(map xs f)g] =
      Expression.listMap (.listMap (.varRef "xs") (.varRef "f")) (.varRef "g") :=
  rfl

-- A conversion produces a list of tuples, which is a list like any other, so a mapping over one is
-- a list's whatever the map it came from was.
example :
    [lgtm| map(toList hashmap(string, int))f] =
      Expression.listMap (.hashmapToList (.hashmapEmpty .string .int)) (.varRef "f") :=
  rfl

-- `map` is a keyword, so it is no variable name inside a DSL term; outside one it is an ordinary
-- Lean identifier, which declaring it with `&` is what preserves.  `list` is one as the keyword of a
-- list type, and takes the same escape hatch.
example : [lgtm| var"map"] = Expression.varRef "map" :=
  rfl

example : [lgtm| var"list"] = Expression.varRef "list" :=
  rfl

-- `flatMap` reads its two operands the way `map` reads its two, and is read by nothing: a list is
-- the one thing there is to flat map over, where there are two to map over.
example : [lgtm| flatMap xs f] = Expression.listFlatMap (.varRef "xs") (.varRef "f") :=
  rfl

example :
    [lgtm| flatMap p.items f] =
      Expression.listFlatMap (.structGet (.varRef "p") "items") (.varRef "f") :=
  rfl

example :
    [lgtm| flatMap g(1)f] =
      Expression.listFlatMap (.app (.varRef "g") [.intLit 1]) (.varRef "f") :=
  rfl

example :
    [lgtm| flatMap[1, 2 : int]f] =
      Expression.listFlatMap (.lcons (.intLit 1) (.lcons (.intLit 2) (.lnil .int)))
        (.varRef "f") :=
  rfl

example : [lgtm| flatMap[ : int]f] = Expression.listFlatMap (.lnil .int) (.varRef "f") :=
  rfl

-- Its function takes one parameter as a list's mapping's does, and returns a list: the keyword is
-- the whole of what tells the two forms apart here, since what the function returns is readable only
-- where it is written out and says nothing about a named `f`.
example :
    [lgtm| flatMap xs (fun (x : int) => [x, x : int])] =
      Expression.listFlatMap (.varRef "xs")
        (.lam [("x", .int)] (.lcons (.varRef "x") (.lcons (.varRef "x") (.lnil .int)))) :=
  rfl

-- What it produces is a list, so every form that reads one reads this, and it reads whatever
-- produces one: a reversal, a length, a cons, a mapping, and another flat mapping.
example :
    [lgtm| reverse(flatMap xs f)] =
      Expression.listReverse (.listFlatMap (.varRef "xs") (.varRef "f")) :=
  rfl

example :
    [lgtm| length(flatMap xs f)] =
      Expression.listLength (.listFlatMap (.varRef "xs") (.varRef "f")) :=
  rfl

example :
    [lgtm| x :: flatMap xs f] =
      Expression.lcons (.varRef "x") (.listFlatMap (.varRef "xs") (.varRef "f")) :=
  rfl

example :
    [lgtm| map(flatMap xs f)g] =
      Expression.listMap (.listFlatMap (.varRef "xs") (.varRef "f")) (.varRef "g") :=
  rfl

example :
    [lgtm| flatMap(map xs g)f] =
      Expression.listFlatMap (.listMap (.varRef "xs") (.varRef "g")) (.varRef "f") :=
  rfl

example :
    [lgtm| flatMap(flatMap xs f)g] =
      Expression.listFlatMap (.listFlatMap (.varRef "xs") (.varRef "f")) (.varRef "g") :=
  rfl

example :
    [lgtm| flatMap(toList m)f] =
      Expression.listFlatMap (.hashmapToList (.varRef "m")) (.varRef "f") :=
  rfl

-- `flatMap` is a keyword, so it is no variable name inside a DSL term, and `var` is the escape
-- hatch.
example : [lgtm| var"flatMap"] = Expression.varRef "flatMap" :=
  rfl

-- `findIndex` reads its two operands the way `flatMap` reads its two, and is read by nothing
-- either: a list is the one thing there is to search.
example : [lgtm| findIndex xs f] = Expression.listFindIndex (.varRef "xs") (.varRef "f") :=
  rfl

example :
    [lgtm| findIndex p.items f] =
      Expression.listFindIndex (.structGet (.varRef "p") "items") (.varRef "f") :=
  rfl

example :
    [lgtm| findIndex g(1)f] =
      Expression.listFindIndex (.app (.varRef "g") [.intLit 1]) (.varRef "f") :=
  rfl

example :
    [lgtm| findIndex[1, 2 : int]f] =
      Expression.listFindIndex (.lcons (.intLit 1) (.lcons (.intLit 2) (.lnil .int)))
        (.varRef "f") :=
  rfl

example : [lgtm| findIndex[ : int]f] = Expression.listFindIndex (.lnil .int) (.varRef "f") :=
  rfl

-- Its predicate takes one parameter at the element type and answers with a `bool`, which is a
-- comparison's answer at a projection's arity — and the keyword is the whole of what says so, since
-- a named `f` shows neither.
example :
    [lgtm| findIndex xs (fun (x : int) => x == 0)] =
      Expression.listFindIndex (.varRef "xs")
        (.lam [("x", .int)] (.equals (.varRef "x") (.intLit 0))) :=
  rfl

-- It reads whatever produces a list, as the other list forms do, and what it produces is an option
-- rather than a list — so a `match` takes it apart where the others hand the next form a list.
example :
    [lgtm| findIndex(reverse xs)f] =
      Expression.listFindIndex (.listReverse (.varRef "xs")) (.varRef "f") :=
  rfl

example :
    [lgtm| findIndex(flatMap xs g)f] =
      Expression.listFindIndex (.listFlatMap (.varRef "xs") (.varRef "g")) (.varRef "f") :=
  rfl

example :
    [lgtm| findIndex(toList m)f] =
      Expression.listFindIndex (.hashmapToList (.varRef "m")) (.varRef "f") :=
  rfl

example :
    [lgtm| match findIndex xs f with | none => 0 | some(i) => i] =
      Expression.optionMatch (.listFindIndex (.varRef "xs") (.varRef "f")) (.intLit 0) "i"
        (.varRef "i") :=
  rfl

-- `findIndex` is a keyword, so it is no variable name inside a DSL term, and `var` is the escape
-- hatch.
example : [lgtm| var"findIndex"] = Expression.varRef "findIndex" :=
  rfl

-- `sortOn` reads its two operands the way `map` reads its two, and is read by nothing: there is one
-- thing to sort, where there are two to map over.
example : [lgtm| sortOn xs f] = Expression.listSortOn (.varRef "xs") (.varRef "f") :=
  rfl

example :
    [lgtm| sortOn p.items f] =
      Expression.listSortOn (.structGet (.varRef "p") "items") (.varRef "f") :=
  rfl

example :
    [lgtm| sortOn g(1)f] = Expression.listSortOn (.app (.varRef "g") [.intLit 1]) (.varRef "f") :=
  rfl

example :
    [lgtm| sortOn[2, 1 : int]f] =
      Expression.listSortOn (.lcons (.intLit 2) (.lcons (.intLit 1) (.lnil .int))) (.varRef "f") :=
  rfl

example : [lgtm| sortOn[ : int]f] = Expression.listSortOn (.lnil .int) (.varRef "f") :=
  rfl

-- The projection takes one parameter, as a list's mapping's function does, and what it returns is
-- the key rather than the element: a sort whose projection returns a `string` is still a sort of
-- the list it was given.
example :
    [lgtm| sortOn xs (fun (x : int) => 0 - x)] =
      Expression.listSortOn (.varRef "xs")
        (.lam [("x", .int)] (.minus (.intLit 0) (.varRef "x"))) :=
  rfl

example :
    [lgtm| sortOn ps (fun (p : struct Point) => p.x)] =
      Expression.listSortOn (.varRef "ps")
        (.lam [("p", .struct "Point")] (.structGet (.varRef "p") "x")) :=
  rfl

-- What it produces is a list, so every form that reads one reads this, and it reads whatever
-- produces one: a reversal, a length, a cons, a mapping, and another sort.
example :
    [lgtm| reverse(sortOn xs f)] =
      Expression.listReverse (.listSortOn (.varRef "xs") (.varRef "f")) :=
  rfl

example :
    [lgtm| length(sortOn xs f)] = Expression.listLength (.listSortOn (.varRef "xs") (.varRef "f")) :=
  rfl

example :
    [lgtm| x :: sortOn xs f] =
      Expression.lcons (.varRef "x") (.listSortOn (.varRef "xs") (.varRef "f")) :=
  rfl

example :
    [lgtm| map(sortOn xs f)g] =
      Expression.listMap (.listSortOn (.varRef "xs") (.varRef "f")) (.varRef "g") :=
  rfl

example :
    [lgtm| sortOn(map xs g)f] =
      Expression.listSortOn (.listMap (.varRef "xs") (.varRef "g")) (.varRef "f") :=
  rfl

example :
    [lgtm| sortOn(sortOn xs f)g] =
      Expression.listSortOn (.listSortOn (.varRef "xs") (.varRef "f")) (.varRef "g") :=
  rfl

example :
    [lgtm| sortOn(toList m)f] = Expression.listSortOn (.hashmapToList (.varRef "m")) (.varRef "f") :=
  rfl

-- `sortOn` is a keyword, so it is no variable name inside a DSL term, and `var` is the escape hatch.
example : [lgtm| var"sortOn"] = Expression.varRef "sortOn" :=
  rfl

-- `sortBy` reads its two operands exactly as `sortOn` reads its two: the keyword is the whole of what
-- tells the two sorts apart here, since what the function takes is readable only where it is written
-- out and says nothing about a named `f`.
example : [lgtm| sortBy xs f] = Expression.listSortBy (.varRef "xs") (.varRef "f") :=
  rfl

example :
    [lgtm| sortBy p.items f] =
      Expression.listSortBy (.structGet (.varRef "p") "items") (.varRef "f") :=
  rfl

example :
    [lgtm| sortBy g(1)f] = Expression.listSortBy (.app (.varRef "g") [.intLit 1]) (.varRef "f") :=
  rfl

example :
    [lgtm| sortBy[2, 1 : int]f] =
      Expression.listSortBy (.lcons (.intLit 2) (.lcons (.intLit 1) (.lnil .int))) (.varRef "f") :=
  rfl

example : [lgtm| sortBy[ : int]f] = Expression.listSortBy (.lnil .int) (.varRef "f") :=
  rfl

-- The comparison takes two parameters where a projection takes one, and returns the answer rather
-- than a key: a `fun` written out is where that becomes visible.
example :
    [lgtm| sortBy xs (fun (a : int) (b : int) => b <= a)] =
      Expression.listSortBy (.varRef "xs")
        (.lam [("a", .int), ("b", .int)] (.le (.varRef "b") (.varRef "a"))) :=
  rfl

example :
    [lgtm| sortBy ps (fun (p : struct Point) (q : struct Point) => p.x < q.x)] =
      Expression.listSortBy (.varRef "ps")
        (.lam [("p", .struct "Point"), ("q", .struct "Point")]
          (.lt (.structGet (.varRef "p") "x") (.structGet (.varRef "q") "x"))) :=
  rfl

-- What it produces is a list, so every form that reads one reads this, and it reads whatever produces
-- one: the two sorts nest into each other as readily as either nests with a mapping.
example :
    [lgtm| reverse(sortBy xs f)] =
      Expression.listReverse (.listSortBy (.varRef "xs") (.varRef "f")) :=
  rfl

example :
    [lgtm| length(sortBy xs f)] = Expression.listLength (.listSortBy (.varRef "xs") (.varRef "f")) :=
  rfl

example :
    [lgtm| x :: sortBy xs f] =
      Expression.lcons (.varRef "x") (.listSortBy (.varRef "xs") (.varRef "f")) :=
  rfl

example :
    [lgtm| map(sortBy xs f)g] =
      Expression.listMap (.listSortBy (.varRef "xs") (.varRef "f")) (.varRef "g") :=
  rfl

example :
    [lgtm| sortBy(sortOn xs f)g] =
      Expression.listSortBy (.listSortOn (.varRef "xs") (.varRef "f")) (.varRef "g") :=
  rfl

example :
    [lgtm| sortOn(sortBy xs f)g] =
      Expression.listSortOn (.listSortBy (.varRef "xs") (.varRef "f")) (.varRef "g") :=
  rfl

example :
    [lgtm| sortBy(toList m)f] = Expression.listSortBy (.hashmapToList (.varRef "m")) (.varRef "f") :=
  rfl

-- `sortBy` is a keyword too, and takes the same escape hatch.
example : [lgtm| var"sortBy"] = Expression.varRef "sortBy" :=
  rfl

/-- The empty map from `string` to `int`: the shortest declaration that returns one, and the one
place the annotations are all there is to go on. -/
@[lgtm] def noneBound as"none-bound" : hashmap string int := hashmap(string, int)

-- A hashmap needs no declaration to be well formed, so this checks against no `TypeDecls` at all.
#guard (noneBound.check {} []).isOk

#guard
  !(({ noneBound with resultType := [lgtm_ty| hashmap int string] } : FuncDecl).check {} []).isOk

/-- `m` with `k` bound to `v`, which is the other half: a binding put into a map rather than read
out of one. -/
@[lgtm] def bind(m : hashmap string int)(k : string)(v : int) : hashmap string int := {m with [k] = v}

#guard (bind.check {} []).isOk

#guard !(({ bind with body := [lgtm| {m with [v] = k}] } : FuncDecl).check {} []).isOk

#guard !(({ bind with resultType := [lgtm_ty| hashmap string string] } : FuncDecl).check {} []).isOk

/-- What `k` is bound to in `m`, and zero when it is bound to nothing: the two halves of a lookup,
which is what an option result is for. -/
@[lgtm] def getOr as"get-or"(m : hashmap string int)(k : string) : int :=
  match m[k] with | none => 0 | some(x) => x

#guard (getOr.check {} []).isOk

#guard !(({ getOr with resultType := [lgtm_ty| option int] } : FuncDecl).check {} []).isOk

#guard
  !(({ getOr with parameters := [("m", [lgtm_ty| hashmap string string]), ("k", .string)] } :
            FuncDecl).check
        {} []).isOk

/-- Every value of `m` with one added to it, the keys left as they were.  The function takes the key
as well as the value, so its parameters are the map's two types in that order.  This is the shape
real code writes a hashmap's mapping in: the type declared for the parameter is what the keyword is
read by, where a fragment needs an operand carrying its own type. -/
@[lgtm] def bump (m : hashmap string int) : hashmap string int :=
  map m (fun (k : string) (v : int) => v + 1)

#guard (bump.check {} []).isOk

example :
    bump.body =
      Expression.hashmapMap (.varRef "m")
        (.lam [("k", .string), ("v", .int)] (.plus (.varRef "v") (.intLit 1))) :=
  rfl

#guard !(({ bump with resultType := [lgtm_ty| hashmap string string] } : FuncDecl).check {} []).isOk

-- The parameters go in the map's two types' order, and the mapping being read as a hashmap's is
-- what holds them to it: the swapped pair is reported against the types the map has.
/-- error: a hashmap's mapping over a hashmap string int needs a function taking (string, int), but this one takes (int, string) -/
#guard_msgs (error) in
@[lgtm] def chkBumpSwapped(m : hashmap string int) : hashmap string int :=
  map m (fun (v : int) (k : string) => v + 1)

-- A mapping is what makes the value type the one thing about a map that can change, since the keys
-- it hands back are the ones it was given: a map to `string` comes out of a map to `int` and the
-- declaration says so.
@[lgtm] def keysOf as"keys-of"(m : hashmap string int) : hashmap string string :=
  map m (fun (k : string) (v : int) => k)

#guard (keysOf.check {} []).isOk

example :
    keysOf.body =
      Expression.hashmapMap (.varRef "m") (.lam [("k", .string), ("v", .int)] (.varRef "k")) :=
  rfl

/-- A mapping over a `let`, which is the other place a declaration's operands get a type: the type
the name is bound at is what the keyword is read by, exactly as a parameter's is. -/
@[lgtm] def bumpNew as"bump-new"(k : string) : hashmap string int :=
  let m := { hashmap(string, int) with [k] = 1 };
  map m (fun (k : string) (v : int) => v + 1)

#guard (bumpNew.check {} []).isOk

example :
    bumpNew.body =
      Expression.let_ "m" (.hashmapPut (.hashmapEmpty .string .int) (.varRef "k") (.intLit 1))
        (.hashmapMap (.varRef "m")
          (.lam [("k", .string), ("v", .int)] (.plus (.varRef "v") (.intLit 1)))) :=
  rfl

-- The key type has to be one a comparison can reach the bottom of, which is the one condition every
-- one of the forms shares and the one way an annotation alone makes a map ill typed.
#guard
  !(({ noneBound with
              body := [lgtm| hashmap((int) -> int, int)]
              resultType := [lgtm_ty| hashmap((int) -> int)int] } :
            FuncDecl).check
        {} []).isOk

-- The *value* type is under no such condition: nothing compares a value a map holds.
#guard
  (({ noneBound with
            body := [lgtm| hashmap(string, (int) -> int)]
            resultType := [lgtm_ty| hashmap string((int) -> int)] } :
          FuncDecl).check
      {} []).isOk

-- And a hashmap is itself not comparable, whatever it relates, where a list of the same things
-- would be: an association list has no canonical form, so a structural comparison would answer
-- something other than whether the two are the same map.
#guard !(({ getOr with body := [lgtm| if m == m then (1) else (0)] } : FuncDecl).check {} []).isOk

#guard
  !(({ noneBound with
              body := [lgtm| hashmap(hashmap string int, int)]
              resultType := [lgtm_ty| hashmap(hashmap string int)int] } :
            FuncDecl).check
        {} []).isOk

-- A tuple expression lists its elements in one group in parentheses, the way the *type* lists its
-- types: the group is what says how many there are, so there is an empty one to write and no
-- annotation anywhere — the elements are what the types are read off.
example : [lgtm| tuple(1, "a")] = Expression.tupleNew [.intLit 1, .stringLit "a"] :=
  rfl

example : [lgtm| tuple("a", 1)] = Expression.tupleNew [.stringLit "a", .intLit 1] :=
  rfl

example : [lgtm| tuple()] = Expression.tupleNew [] :=
  rfl

example : [lgtm| tuple(1)] = Expression.tupleNew [.intLit 1] :=
  rfl

example :
    [lgtm| tuple(1, "a", true)] = Expression.tupleNew [.intLit 1, .stringLit "a", .boolLit true] :=
  rfl

example :
    [lgtm| tuple(x + 1, p.y)] =
      Expression.tupleNew [.plus (.varRef "x") (.intLit 1), .structGet (.varRef "p") "y"] :=
  rfl

example :
    [lgtm| tuple(tuple(1), "a")] = Expression.tupleNew [.tupleNew [.intLit 1], .stringLit "a"] :=
  rfl

-- `tuple` is a keyword, so it is no variable name inside a DSL term; outside one it is an ordinary
-- Lean identifier, which declaring it with `&` is what preserves.
example : [lgtm| var"tuple"] = Expression.varRef "tuple" :=
  rfl

-- A read is written like a field read with an index in place of the name, binds as tightly as one,
-- and nests into the other postfix forms the same way.
example : [lgtm| t.0] = Expression.tupleGet (.varRef "t") 0 :=
  rfl

example : [lgtm| t.1] = Expression.tupleGet (.varRef "t") 1 :=
  rfl

example : [lgtm| t.10] = Expression.tupleGet (.varRef "t") 10 :=
  rfl

example : [lgtm| p.t.0] = Expression.tupleGet (.structGet (.varRef "p") "t") 0 :=
  rfl

example : [lgtm| f(1).0] = Expression.tupleGet (.app (.varRef "f") [.intLit 1]) 0 :=
  rfl

example : [lgtm| m[k].0] = Expression.tupleGet (.hashmapGet (.varRef "m") (.varRef "k")) 0 :=
  rfl

example : [lgtm| tuple(1, "a").0] = Expression.tupleGet (.tupleNew [.intLit 1, .stringLit "a"]) 0 :=
  rfl

-- What it does not nest into is itself, because Lean's tokenizer reads `0.1` as a decimal and `0.x`
-- as an attempt at one.  Parentheses are what say which `.` is which, the same way they do for the
-- two `:`s of `[(none : int) : option int]`.
example : [lgtm| (t.0).1] = Expression.tupleGet (.tupleGet (.varRef "t") 0) 1 :=
  rfl

example : [lgtm| (t.0).x] = Expression.structGet (.tupleGet (.varRef "t") 0) "x" :=
  rfl

-- And what a read produces is an ordinary operand, so the looser operators take one without
-- parentheses.
example : [lgtm| t.0 + 1] = Expression.plus (.tupleGet (.varRef "t") 0) (.intLit 1) :=
  rfl

example :
    [lgtm| t.0 == t.1] =
      Expression.equals (.tupleGet (.varRef "t") 0) (.tupleGet (.varRef "t") 1) :=
  rfl

example : [lgtm| reverse tuple(1)] = Expression.listReverse (.tupleNew [.intLit 1]) :=
  rfl

/-- The pair of its two arguments: the shortest declaration whose result type is a tuple, and the
one place the element types are the arguments' and nothing else. -/
@[lgtm] def pair(s : string)(n : int) : tuple(string, int) := tuple(s, n)

-- A tuple needs no declaration to be well formed, so this checks against no `TypeDecls` at all.
#guard (pair.check {} []).isOk

#guard !(({ pair with resultType := [lgtm_ty| tuple(int, string)] } : FuncDecl).check {} []).isOk

#guard !(({ pair with resultType := [lgtm_ty| tuple(string)] } : FuncDecl).check {} []).isOk

#guard !(({ pair with resultType := [lgtm_ty| list string] } : FuncDecl).check {} []).isOk

/-- The first half of a pair, which is the other half: a value read out of a tuple rather than put
into one. -/
@[lgtm] def fst(t : tuple(string, int)) : string := t.0

#guard (fst.check {} []).isOk

#guard
  (({ fst with
            body := [lgtm| t.1], resultType := .int } :
          FuncDecl).check
      {} []).isOk

-- An index past the end is ill typed, which is what makes the index a literal: the type at a
-- position that is not known until something runs is a type nothing could report.
#guard !(({ fst with body := [lgtm| t.2] } : FuncDecl).check {} []).isOk

#guard !(({ fst with body := [lgtm| t.1] } : FuncDecl).check {} []).isOk

-- A tuple is comparable exactly when everything in it is, so a pair of a map is not and a pair of
-- its two types is: what `Ty.comparable` turns a hashmap down for is the order its bindings are
-- carried in, which converting does not escape.
#guard (({ fst with body := [lgtm| if t == t then (t.0) else (t.0)] } : FuncDecl).check {} []).isOk

#guard
  !(({ fst with
              parameters := [("t", [lgtm_ty| tuple(string, hashmap string int)])]
              body := [lgtm| if t == t then (t.0) else (t.0)] } :
            FuncDecl).check
        {} []).isOk

/-- The bindings of a map as a list of pairs, which is the type `toList` gives one: the form a
`tuple` is in the IR for. -/
@[lgtm] def bindings(m : hashmap string int) : list tuple(string, int) := toList m

#guard (bindings.check {} []).isOk

#guard
  !(({ bindings with resultType := [lgtm_ty| list tuple(int, string)] } : FuncDecl).check {}
        []).isOk

-- An unreachable branch is written with its annotation, which is read the way `none`'s is: a type
-- at `max`, so everything but a function type goes without parentheses.
example : [lgtm| unreachable"why" : int] = Expression.unreachable .int "why" :=
  rfl

example : [lgtm| unreachable"why" : list int] = Expression.unreachable (.list .int) "why" :=
  rfl

example : [lgtm| unreachable"why" : option int] = Expression.unreachable (.option .int) "why" :=
  rfl

example :
    [lgtm| unreachable"why" : struct Point] = Expression.unreachable (.struct "Point") "why" :=
  rfl

example :
    [lgtm| unreachable"why" : tuple(string, int)] =
      Expression.unreachable (.tuple [.string, .int]) "why" :=
  rfl

example :
    [lgtm| unreachable"why" : ((int) -> int)] = Expression.unreachable (.fn [.int] .int) "why" :=
  rfl

-- It stands where a value of its annotation would, and `unreachable` is a keyword, so a variable of
-- that name takes the escape hatch every other keyword leaves.
example :
    [lgtm| if b then (1) else (unreachable"why" : int)] =
      Expression.ite (.varRef "b") (.intLit 1) (.unreachable .int "why") :=
  rfl

example :
    [lgtm| unreachable"why" : int + 1] = Expression.plus (.unreachable .int "why") (.intLit 1) :=
  rfl

example :
    [lgtm| f(unreachable"why" : int)] = Expression.app (.varRef "f") [.unreachable .int "why"] :=
  rfl

example : [lgtm| var"unreachable"] = Expression.varRef "unreachable" :=
  rfl

-- As with `none : T`, DSL code parenthesizes the annotation so the text is shaped like a Lean
-- ascription; the `Expression` is the same one the bare form builds.
example : [lgtm| (unreachable"why" : int)] = Expression.unreachable .int "why" :=
  rfl

/-- One less than a positive `n`, with the branch that would have gone negative written as the
unreachable it is: the annotation is the `int` the branch beside it has, and nothing else about the
form is the type checker's business. -/
@[lgtm] def pred(n : int) : int := if 0 < n then (n - 1) else (unreachable"n is positive" : int)

#guard (pred.check {} []).isOk

#guard !(({ pred with resultType := [lgtm_ty| string] } : FuncDecl).check {} []).isOk

-- The annotation has to be the branch's type, which is the one thing it is checked against.
#guard
  !(({ pred with
              body := [lgtm| if 0 < n then (n - 1) else (unreachable"n is positive" : string)] } :
            FuncDecl).check
        {} []).isOk

/-! ## What a command checks where it is written

The declarations below are wrong on purpose, and what is checked is the message each draws and the
token it lands on: `#guard_msgs` fails if a command reports anything other than what is written
above it, which is also how it is checked that a *correct* declaration reports nothing at all.

The commands report rather than throw, so the Lean declaration is still made and the errors of one
declaration do not bury the next.  See the "What the commands do besides declare" section of
`LgtmDeepLean.Lang.Syntax`. -/

@[lgtm] structure ChkPt where
  x : int
  y : int

@[lgtm] inductive ChkHue where
  | Dark
  | Rgb(int, int, int)

@[lgtm] def chkPtX(p : struct ChkPt) : int := p.x

/-! ### Names

A name is resolved against the parameters and `let`s it is written under and the declarations in
scope, and one neither of them has is reported on the token itself. -/

/-- error: no variable named 'q' is in scope; did you mean 'p'? -/
#guard_msgs (error) in
@[lgtm] def chkUnbound(p : struct ChkPt) : int := q

-- A dotted name is either one declaration or a field read of a variable, so one that is neither is
-- reported over the whole of it: what it was meant to be is far more often the declaration.
/-- error: nothing named 'q.x' is declared, and 'q' is not a variable in scope -/
#guard_msgs (error) in
@[lgtm] def chkDotted(p : struct ChkPt) : int := q.x

@[lgtm] def Threads.asAlist.sortThreadLists(n : int) : int := n

-- Four edits apart and over twenty characters long is a rename rather than a coincidence, and is
-- said to be.  This is the mistake the model had in it when the checking was added.
/--
error: nothing named 'Threads.asAlist.sortThreads' is declared, and 'Threads' is not a variable in scope; did you mean 'Threads.asAlist.sortThreadLists'?
-/
#guard_msgs (error) in
@[lgtm] def chkRenamed(n : int) : int := Threads.asAlist.sortThreads(n)

/-- error: 'ChkPt' is a struct, not an inductive type: write `struct ChkPt` -/
#guard_msgs (error) in
@[lgtm] def chkWrongKind(p : inductive ChkPt) : int := 1

/-- error: 'ChkHue' is an inductive type, not a struct: write `inductive ChkHue` -/
#guard_msgs (error) in
@[lgtm] def chkWrongKind2(h : struct ChkHue) : int := 1

-- A field's type is a name like any other, which `Program.check` never looks at: it checks the
-- bodies of declarations, so a field of a type nothing declares is a mistake only this reports.
/-- error: no struct named 'Nope' is declared -/
#guard_msgs (error) in
@[lgtm] structure ChkNoSuchField where
  f : struct Nope

/-- error: struct 'ChkPt' has no field named 'z'; did you mean 'x'? -/
#guard_msgs (error) in
@[lgtm] def chkBadField : struct ChkPt := new ChkPt{z = 1, y = 2}

/-- error: inductive 'ChkHue' has no constructor named 'Darkk'; did you mean 'Dark'? -/
#guard_msgs (error) in
@[lgtm] def chkBadCtor : inductive ChkHue := new ChkHue.Darkk()

/-- error: constructor 'Rgb' of inductive 'ChkHue' carries 3 value(s), but 1 are given here -/
#guard_msgs (error) in
@[lgtm] def chkBadCtorArity : inductive ChkHue := new ChkHue.Rgb(1)

/-- error: 'chkPtX' takes 1 argument(s), but 2 are given here -/
#guard_msgs (error) in
@[lgtm] def chkBadArity(p : struct ChkPt) : int := chkPtX(p, p)

-- A `let` binds for its body and nowhere else, so the second mention of `m` is out of scope rather
-- than ill typed, and is reported on the name.
/-- error: no variable named 'm' is in scope; did you mean 'n'? -/
#guard_msgs (error) in
@[lgtm] def chkLetEscapes(n : int) : int := (let m := n + 1; m) + m

/-! ### Types

A declaration whose names all resolve is type checked, and what is reported lands on the innermost
part of it that does not check rather than on the whole body. -/

/-- error: the left operand of `+` has type struct ChkPt where int was expected -/
#guard_msgs (error) in
@[lgtm] def chkDeepTypeError(p : struct ChkPt)(n : int) : int :=
  let a := n + 1;
  (a + (p + 1)) + 3

/-- error: the `else` branch of an `if` has type string where int was expected -/
#guard_msgs (error) in
@[lgtm] def chkBadBranch(b : bool)(n : int) : int := n + (if b then (1) else ("two"))

-- A body that checks but not at the type declared for it is a disagreement between the two rather
-- than a mistake inside the body, and is reported on the body.
/-- error: this expression has type int where string was expected -/
#guard_msgs (error) in
@[lgtm] def chkWrongResult(n : int) : string := n + 1

-- A name nothing declares is reported once.  The type checker would reach it again, one form out,
-- and say the same thing about more of the term, so a declaration that has had something said
-- about it is not then checked.
/-- error: no variable named 'zzqqxx' is in scope -/
#guard_msgs (error) in
@[lgtm] def chkOneErrorOnly(n : int) : string := zzqqxx + 1

/-! ### What is not reported

A correct declaration reports nothing, and neither does a bare `[lgtm| ...]`: a fragment has no
context in which a name could be wrong, so it is read but not resolved. -/

#guard_msgs (error) in
@[lgtm] def chkFine(p : struct ChkPt) : int := chkPtX(p) + p.y

#guard_msgs (error) in
example : [lgtm| anything.at.all + unknownName] =
    Expression.plus (.structGet (.structGet (.varRef "anything") "at") "all")
      (.varRef "unknownName") :=
  rfl

-- A declaration may call itself: its own name and signature are in scope for its body.
#guard_msgs (error) in
@[lgtm] def chkCountdown(n : int) : int := chkCountdown(n - 1)

-- And a struct may hold a value of its own type.
#guard_msgs (error) in
@[lgtm] structure ChkNest where
  kids : list (struct ChkNest)

-- Two that call each other need `@[lgtm, forward]`, which declares a signature and no Lean
-- declaration.
#guard_msgs (error) in
@[lgtm, forward] def chkEvenish(n : int) : bool

#guard_msgs (error) in
@[lgtm] def chkOddish(n : int) : bool := chkEvenish(n - 1)

#guard_msgs (error) in
@[lgtm] def chkEvenish(n : int) : bool := chkOddish(n - 1)

/-! ### A term with a splice in it is not checked here

A splice is a Lean term, so the value a command builds around one has a marker where an expression
should be and is not what the writer wrote.  Nothing is reported about it, and `Program.check` is
what checks it. -/

#guard_msgs (error) in
@[lgtm] def chkSpliced(n : int) : string := ~(Expression.plus (.varRef "n") (.intLit 1))

#guard !(chkSpliced.check {} []).isOk

/-! ## The commands are shaped like the Lean declarations they generate

Each command is spelled as an attribute and then `def`, `structure` or `inductive`, with a
`structure`'s fields and an `inductive`'s constructors one to a line under a `where`.  What that
buys is a file of DSL declarations that a tool reading Lean by its grammar can get through, and what
it costs is nothing: the declarations below are Lean's own, written in a module that imports this
syntax, and they still mean what they always did. -/

@[simp] theorem lgtmAttrLeavesLeanAttrsAlone : 1 + 1 = 2 :=
  rfl

@[inline] private def leanDefStillParses (n : Nat) : Nat :=
  n + 1

example : leanDefStillParses 1 = 2 :=
  rfl

private structure LeanStructStillParses where
  f : Nat

private inductive LeanIndStillParses where
  | a
  | b

example : (LeanStructStillParses.mk 1).f = 1 :=
  rfl

-- `@[lgtm]` is one token of its own and the `forward` form spells both of its words with `&`, so
-- `lgtm` is not reserved and is an ordinary Lean name.
private def lgtm : Nat :=
  0

example : lgtm = 0 :=
  rfl

-- A field list ends where its indentation does: the command after one is a command and not a field
-- of it, which is what `manyIndent` is for.  `EndsAtIndent` has the two fields written and no
-- more, and the `def` under it is its own declaration.
@[lgtm] private structure EndsAtIndent where
  x : int
  y : int

private def notAFieldOfEndsAtIndent : Nat :=
  1

example : EndsAtIndent.fields = [("x", .int), ("y", .int)] :=
  rfl

example : notAFieldOfEndsAtIndent = 1 :=
  rfl

-- And a declaration with nothing under the `where` is followed by whatever comes next, which the
-- empty list of fields and the empty list of constructors below are read with.
@[lgtm] private structure NoFieldsAtAll where

@[lgtm] private inductive NoCtorsAtAll as"no-ctors-at-all" where

example : NoFieldsAtAll.fields = [] :=
  rfl

example : NoCtorsAtAll = { name := "no-ctors-at-all", constructors := [] } :=
  rfl
