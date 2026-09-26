module

public import LgtmDeepLean.IR
public import LgtmDeepLean.TypeCheck
meta import LgtmDeepLean.IR
meta import LgtmDeepLean.TypeCheck

/-! # Surface syntax for the IR

An `Expression` written out of its constructors stops being readable at about three nodes:
`.lcons (.stringLit "!") (.lcons (.varRef "s") (.lnil .string))` is a two-element list.  This module
adds notation for `Ty`, `Expression`, and `Decl` so the same programs can be written the way the
docstrings elsewhere already describe them — `fun (x : int) => x + 1`, `g(x)`, `x :: xs`.

Three entry points:

* `[lgtm_ty| (int) -> string]` elaborates to a `Ty`.
* `[lgtm| fun (x : int) => x + 1]` elaborates to an `Expression`.
* `lgtm def` is a command that declares a `Decl`.

Everything is a macro, so these expand to ordinary constructor applications and cost nothing at
run time.  A DSL term is *not* checked by `Expression.infer` when it elaborates — `[lgtm| 1 + "a"]`
is a perfectly good `Expression` that happens to be ill typed.  Type checking stays where it was,
in `Expression.check` and `Decl.check`.

Scoping is the IR's, not Lean's: an identifier always becomes a `varRef` of its own name, so the
`x` in `[lgtm| fun (x : int) => x]` refers to the DSL binder and never to a Lean variable called
`x`.  To reach a Lean term of type `Expression` or `Ty`, splice it with `~(...)`.

The keywords inside a DSL term — `int`, `string`, `list`, `reverse`, `var`, and `as` — are declared
with `&`, Lean's non-reserved symbol form, so importing this module does not stop `int` or `list`
from being used as ordinary Lean identifiers.  `lgtm` is the one exception and *is* a reserved
token: a command's leading keyword has to be reserved for the command parser to find it at all, so
a file importing this module cannot also name something `lgtm`.
-/

/-! `behavior := symbol` is what lets the keywords be non-reserved: it tells the category to consider
its symbol parsers when it meets an identifier, which is how `&"int"` gets a chance to match at all.
Without it a category ignores `&`-declared alternatives entirely. -/

declare_syntax_cat lgtmTy (behavior := symbol)
declare_syntax_cat lgtmExpr (behavior := symbol)

/-! ## Types

`Ty.fn` records every parameter at once, so a function type is written with its parameters in one
comma-separated group: `(int, string) -> int`, and `() -> int` for a function of no arguments. -/

syntax:max &"int" : lgtmTy
syntax:max &"string" : lgtmTy
syntax:max &"list" lgtmTy:max : lgtmTy
syntax:max "(" lgtmTy ")" : lgtmTy
syntax:20 "(" lgtmTy,* ")" " -> " lgtmTy:20 : lgtmTy
syntax:max "~" "(" term ")" : lgtmTy

/-- `[lgtm_ty| t]` is the `Ty` that `t` denotes. -/
syntax:max "[lgtm_ty| " lgtmTy "]" : term

macro_rules
  | `([lgtm_ty| int]) => `(Ty.int)
  | `([lgtm_ty| string]) => `(Ty.string)
  | `([lgtm_ty| list $t]) => `(Ty.list [lgtm_ty| $t])
  | `([lgtm_ty| ($t)]) => `([lgtm_ty| $t])
  | `([lgtm_ty| ($ts,*) -> $r]) => do
      let ps ← ts.getElems.mapM fun t => `([lgtm_ty| $t])
      `(Ty.fn [$ps,*] [lgtm_ty| $r])
  | `([lgtm_ty| ~($t)]) => `(($t : Ty))

/-! ## Expressions

Precedence runs `::` looser than `+`/`-`, which are looser than application and `reverse`, so
`1 + 2 :: xs` is `(1 + 2) :: xs` and `f(x) + 1` is `(f(x)) + 1`.

A list literal carries its element type, because `lnil` does: `[1, 2 : int]` is
`.lcons (.intLit 1) (.lcons (.intLit 2) (.lnil .int))`, and the empty list is `[: int]`. -/

syntax:max ident : lgtmExpr
syntax:max num : lgtmExpr
syntax:max str : lgtmExpr
syntax:max "(" lgtmExpr ")" : lgtmExpr
syntax:max "~" "(" term ")" : lgtmExpr
/-- `var "x"` is the variable `x`, for IR names that are not Lean identifiers. -/
syntax:max &"var" str : lgtmExpr
syntax:max "[" lgtmExpr,* " : " lgtmTy "]" : lgtmExpr
syntax:max &"reverse" lgtmExpr:max : lgtmExpr
syntax:max lgtmExpr:max noWs "(" lgtmExpr,* ")" : lgtmExpr
syntax:65 lgtmExpr:65 " + " lgtmExpr:66 : lgtmExpr
syntax:65 lgtmExpr:65 " - " lgtmExpr:66 : lgtmExpr
syntax:55 lgtmExpr:56 " :: " lgtmExpr:55 : lgtmExpr
syntax:10 "fun" ("(" ident " : " lgtmTy ")")* " => " lgtmExpr:10 : lgtmExpr

/-- `[lgtm| e]` is the `Expression` that `e` denotes. -/
syntax:max "[lgtm| " lgtmExpr "]" : term

macro_rules
  | `([lgtm| $x:ident]) => `(Expression.varRef $(Lean.quote x.getId.toString))
  | `([lgtm| var $s:str]) => `(Expression.varRef $s)
  | `([lgtm| $n:num]) => `(Expression.intLit $n)
  | `([lgtm| $s:str]) => `(Expression.stringLit $s)
  | `([lgtm| ($e)]) => `([lgtm| $e])
  | `([lgtm| ~($e)]) => `(($e : Expression))
  | `([lgtm| $a + $b]) => `(Expression.plus [lgtm| $a] [lgtm| $b])
  | `([lgtm| $a - $b]) => `(Expression.minus [lgtm| $a] [lgtm| $b])
  | `([lgtm| $a :: $b]) => `(Expression.lcons [lgtm| $a] [lgtm| $b])
  | `([lgtm| reverse $e]) => `(Expression.listReverse [lgtm| $e])
  | `([lgtm| [$es,* : $t]]) => do
      let mut acc ← `(Expression.lnil [lgtm_ty| $t])
      for e in es.getElems.reverse do
        acc ← `(Expression.lcons [lgtm| $e] $acc)
      return acc
  | `([lgtm| $f($args,*)]) => do
      let as ← args.getElems.mapM fun a => `([lgtm| $a])
      `(Expression.app [lgtm| $f] [$as,*])
  | `([lgtm| fun $[($xs:ident : $ts:lgtmTy)]* => $b]) => do
      let ps ← (xs.zip ts).mapM fun (x, t) =>
        `(($(Lean.quote x.getId.toString), [lgtm_ty| $t]))
      `(Expression.lam [$ps,*] [lgtm| $b])

/-! ## Declarations -/

/-- The visibility of a `lgtm def`.  `public` because a `module` hides even the names of its own
parser aliases otherwise, and this one is referred to by the command syntax below. -/
public syntax lgtmVis := "private "

/-- `lgtm def f (x : int) : int := body` declares `f : Decl`.

The IR name defaults to the Lean name; `as "f-name"` overrides it, which is what IR names that are
not Lean identifiers need.  A doc comment becomes the `Decl.docstring` field as well as the Lean
declaration's own documentation.

The parameters are the `Decl`'s parameter list and so are also the context its body is checked in;
they are not Lean binders.

`lgtm private def` makes the generated Lean declaration `private`.  The visibility comes after
`lgtm` rather than before it because a command's first token is what the parser dispatches on. -/
syntax (docComment)? "lgtm " (lgtmVis)? "def " ident (&"as" str)?
  ("(" ident " : " lgtmTy ")")* " : " lgtmTy " := " lgtmExpr : command

macro_rules
  | `($[$doc:docComment]? lgtm $[$vis:lgtmVis]? def $n:ident $[as $ir:str]?
        $[($xs:ident : $ts:lgtmTy)]* : $rt:lgtmTy := $body:lgtmExpr) => do
      let ps ← (xs.zip ts).mapM fun (x, t) =>
        `(($(Lean.quote x.getId.toString), [lgtm_ty| $t]))
      let irName := ir.getD (Lean.quote n.getId.toString)
      let docText := match doc with
        | some d => d.getDocString.trimAscii.toString
        | none => ""
      let val ← `({ docstring := $(Lean.quote docText)
                    name := $irName
                    parameters := [$ps,*]
                    body := [lgtm| $body]
                    resultType := [lgtm_ty| $rt] : Decl })
      match vis with
      | some _ => `($[$doc:docComment]? private def $n : Decl := $val)
      | none => `($[$doc:docComment]? def $n : Decl := $val)

section Tests

-- Types elaborate to the constructors they describe, `fn` taking all its parameters at once.
example : [lgtm_ty| int] = Ty.int := rfl
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

-- Identifiers are IR names, never Lean ones: `n` below is a `varRef`, not this Lean `n`.
private def n : Expression := .intLit 99
example : [lgtm| n] = Expression.varRef "n" := rfl

-- Splicing is how a Lean term gets in.
example : [lgtm| ~(n) + 1] = Expression.plus (.intLit 99) (.intLit 1) := rfl
example : [lgtm_ty| list ~(Ty.int)] = Ty.list .int := rfl

/-- Add `x` to one less than `y`. -/
lgtm def addPred as "add-pred" (x : int) (y : int) : int :=
  x + (y - 1)

-- The command builds the `Decl` field by field: the doc comment, the `as` name, the parameters in
-- order, the body, and the result type.
example : addPred =
    { docstring := "Add `x` to one less than `y`."
      name := "add-pred"
      parameters := [("x", .int), ("y", .int)]
      body := .plus (.varRef "x") (.minus (.varRef "y") (.intLit 1))
      resultType := .int } := rfl

-- And what it builds type checks, which is the point of writing it this way.
#guard addPred.check []

/-- Put `s` after an exclamation mark. -/
lgtm def bang (s : string) : list string :=
  ["!", s : string]

-- With no `as`, the IR name is the Lean name.
example : bang.name = "bang" := rfl
#guard bang.check []

lgtm def applyTo as "apply-to" (g : (int) -> int) (x : int) : int :=
  g(x)

#guard applyTo.check []

/-- Build a function that adds `n` to its argument. -/
lgtm def adder (n : int) : (int) -> int :=
  fun (m : int) => n + m

#guard adder.check []

/-- Reverse `xs` with `x` on the front. -/
lgtm def revCons as "rev-cons" (x : int) (xs : list int) : list int :=
  reverse (x :: xs)

#guard revCons.check []

-- A declaration with no parameters is fine, and so is one that returns a function.
lgtm def three : int := 3
#guard three.check []

-- `lgtm private def` makes the Lean declaration private; the `Decl` it builds is the same.
/-- One more than `x`. -/
lgtm private def succ as "succ-one" (x : int) : int := x + 1
example : succ.name = "succ-one" := rfl
example : succ.docstring = "One more than `x`." := rfl
#guard succ.check []

-- The DSL builds ill-typed programs as readily as well-typed ones; checking is still what rejects
-- them.
#guard !({ three with body := [lgtm| 1 + "a"] } : Decl).check []
#guard !({ revCons with body := [lgtm| reverse x] } : Decl).check []

end Tests
