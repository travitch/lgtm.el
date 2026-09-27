module

public import LgtmDeepLean.Lang.IR
public import LgtmDeepLean.Lang.TypeCheck
meta import LgtmDeepLean.Lang.IR
meta import LgtmDeepLean.Lang.TypeCheck

/-! # Surface syntax for the IR

An `Expression` written out of its constructors stops being readable at about three nodes:
`.lcons (.stringLit "!") (.lcons (.varRef "s") (.lnil .string))` is a two-element list.  This module
adds notation for `Ty`, `Expression`, and `Decl` so the same programs can be written the way the
docstrings elsewhere already describe them — `fun (x : int) => x + 1`, `g(x)`, `x :: xs`.

Four entry points:

* `[lgtm_ty| (int) -> string]` elaborates to a `Ty`.
* `[lgtm| fun (x : int) => x + 1]` elaborates to an `Expression`.
* `lgtm def` is a command that declares a `Decl`.
* `lgtm struct` is a command that declares a `StructDecl`.

Everything is a macro, so these expand to ordinary constructor applications and cost nothing at
run time.  A DSL term is *not* checked by `Expression.infer` when it elaborates — `[lgtm| 1 + "a"]`
is a perfectly good `Expression` that happens to be ill typed.  Type checking stays where it was,
in `Expression.check` and `Decl.check`.

Scoping is the IR's, not Lean's: an identifier always becomes a `varRef` of its own name, so the
`x` in `[lgtm| fun (x : int) => x]` refers to the DSL binder and never to a Lean variable called
`x`.  To reach a Lean term of type `Expression` or `Ty`, splice it with `~(...)`.

The keywords inside a DSL term — `int`, `string`, `list`, `reverse`, `var`, `struct`, `new`, and `as`
— are declared with `&`, Lean's non-reserved symbol form, so importing this module does not stop
`int` or `list` from being used as ordinary Lean identifiers.  `lgtm` is the one exception and *is* a
reserved token: a command's leading keyword has to be reserved for the command parser to find it at
all, so a file importing this module cannot also name something `lgtm`.

`let`, `in`, and `with` are written as plain symbols rather than with `&`, because Lean reserves all
three already: declaring them here takes nothing away that was available before.
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
/-- `struct Point` is the type the `lgtm struct` named `Point` declares.  The string form,
`struct "my-struct"`, is for struct names that are not Lean identifiers — the same escape hatch
`var` is for variables. -/
syntax:max &"struct" ident : lgtmTy
syntax:max &"struct" str : lgtmTy
syntax:max "(" lgtmTy ")" : lgtmTy
syntax:20 "(" lgtmTy,* ")" " -> " lgtmTy:20 : lgtmTy
syntax:max "~" "(" term ")" : lgtmTy

/-- `[lgtm_ty| t]` is the `Ty` that `t` denotes. -/
syntax:max "[lgtm_ty| " lgtmTy "]" : term

macro_rules
  | `([lgtm_ty| int]) => `(Ty.int)
  | `([lgtm_ty| string]) => `(Ty.string)
  | `([lgtm_ty| list $t]) => `(Ty.list [lgtm_ty| $t])
  | `([lgtm_ty| struct $n:ident]) => `(Ty.struct $(Lean.quote n.getId.toString))
  | `([lgtm_ty| struct $n:str]) => `(Ty.struct $n)
  | `([lgtm_ty| ($t)]) => `([lgtm_ty| $t])
  | `([lgtm_ty| ($ts,*) -> $r]) => do
      let ps ← ts.getElems.mapM fun t => `([lgtm_ty| $t])
      `(Ty.fn [$ps,*] [lgtm_ty| $r])
  | `([lgtm_ty| ~($t)]) => `(($t : Ty))

/-! ## Expressions

Precedence runs `::` looser than `+`/`-`, which are looser than application and `reverse`, so
`1 + 2 :: xs` is `(1 + 2) :: xs` and `f(x) + 1` is `(f(x)) + 1`.

A list literal carries its element type, because `lnil` does: `[1, 2 : int]` is
`.lcons (.intLit 1) (.lcons (.intLit 2) (.lnil .int))`, and the empty list is `[: int]`.

The three struct forms are `new Point { x = 1, y = 2 }`, `p.x`, and `{ p with x = 1 }`.  A field read
is written two ways for one reason: `p.x` is a single identifier token as far as Lean's tokenizer is
concerned, so a dotted identifier is split into a `varRef` and one `structGet` per component, while
the postfix `.` is what reads a field of something that is not a bare name — `f(1).x`, or
`(var "my-struct").x`.  The two agree on everything they both accept. -/

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
/-- `new Point { x = 1, y = 2 }` builds a `Point`.  Every field the declaration has must be given,
in the order it declares them, which is the type checker's business rather than the parser's. -/
syntax:max &"new" ident "{" (ident " = " lgtmExpr),* "}" : lgtmExpr
syntax:max &"new" str "{" (ident " = " lgtmExpr),* "}" : lgtmExpr
/-- `e.field`, for an `e` that is not a bare name.  A bare name takes the dotted-identifier route
instead. -/
syntax:max lgtmExpr:max noWs "." noWs ident : lgtmExpr
/-- `{ p with x = 1, y = 2 }` is `p` with those fields rebound and the rest left alone. -/
syntax:max "{" lgtmExpr " with " (ident " = " lgtmExpr),* "}" : lgtmExpr
syntax:65 lgtmExpr:65 " + " lgtmExpr:66 : lgtmExpr
syntax:65 lgtmExpr:65 " - " lgtmExpr:66 : lgtmExpr
syntax:55 lgtmExpr:56 " :: " lgtmExpr:55 : lgtmExpr
syntax:10 "fun" ("(" ident " : " lgtmTy ")")* " => " lgtmExpr:10 : lgtmExpr
/-- `let x = e in body`.  The bound expression carries no annotation, because `let_` does not: the
type checker infers it.  The body extends as far right as it can, so `let`s chain without
parentheses. -/
syntax:10 "let " ident " = " lgtmExpr " in " lgtmExpr:10 : lgtmExpr

/-- `[lgtm| e]` is the `Expression` that `e` denotes. -/
syntax:max "[lgtm| " lgtmExpr "]" : term

macro_rules
  | `([lgtm| $x:ident]) => do
      -- `p.x.y` arrives here as one identifier, because that is how it tokenizes: the first
      -- component is the variable and each one after it is a field read of what came before.
      match x.getId.toString.splitOn "." with
      | [] => Lean.Macro.throwUnsupported
      | root :: fields =>
          let mut acc ← `(Expression.varRef $(Lean.quote root))
          for f in fields do
            acc ← `(Expression.structGet $acc $(Lean.quote f))
          return acc
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
  | `([lgtm| let $x:ident = $e in $b]) =>
      `(Expression.let_ $(Lean.quote x.getId.toString) [lgtm| $e] [lgtm| $b])
  | `([lgtm| new $n:ident { $[$fs:ident = $es:lgtmExpr],* }]) => do
      let bs ← (fs.zip es).mapM fun (f, e) => `(($(Lean.quote f.getId.toString), [lgtm| $e]))
      `(Expression.structNew $(Lean.quote n.getId.toString) [$bs,*])
  | `([lgtm| new $n:str { $[$fs:ident = $es:lgtmExpr],* }]) => do
      let bs ← (fs.zip es).mapM fun (f, e) => `(($(Lean.quote f.getId.toString), [lgtm| $e]))
      `(Expression.structNew $n [$bs,*])
  | `([lgtm| $e.$f:ident]) => do
      let mut acc ← `([lgtm| $e])
      for g in f.getId.toString.splitOn "." do
        acc ← `(Expression.structGet $acc $(Lean.quote g))
      return acc
  | `([lgtm| { $e with $[$fs:ident = $es:lgtmExpr],* }]) => do
      let bs ← (fs.zip es).mapM fun (f, e) => `(($(Lean.quote f.getId.toString), [lgtm| $e]))
      `(Expression.structUpdate [lgtm| $e] [$bs,*])

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

/-- `lgtm struct Point { x : int, y : int }` declares `Point : StructDecl`.

The same shape as `lgtm def`: the IR name defaults to the Lean name and `as "point"` overrides it,
and `lgtm private struct` makes the generated Lean declaration `private`.  The fields are in the
order they are written, which is the order a `new` has to give them in.

A doc comment documents the Lean declaration only.  A `StructDecl` has no docstring field to put it
in, unlike a `Decl`. -/
syntax (docComment)? "lgtm " (lgtmVis)? &"struct" ident (&"as" str)?
  "{" (ident " : " lgtmTy),* "}" : command

macro_rules
  | `($[$doc:docComment]? lgtm $[$vis:lgtmVis]? struct $n:ident $[as $ir:str]?
        { $[$fs:ident : $ts:lgtmTy],* }) => do
      let fields ← (fs.zip ts).mapM fun (f, t) =>
        `(($(Lean.quote f.getId.toString), [lgtm_ty| $t]))
      let irName := ir.getD (Lean.quote n.getId.toString)
      let val ← `({ name := $irName, fields := [$fields,*] : StructDecl })
      match vis with
      | some _ => `($[$doc:docComment]? private def $n : StructDecl := $val)
      | none => `($[$doc:docComment]? def $n : StructDecl := $val)

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

-- A declaration with no parameters is fine, and so is one that returns a function.
lgtm def three : int := 3
#guard three.check {} []

-- `lgtm private def` makes the Lean declaration private; the `Decl` it builds is the same.
/-- One more than `x`. -/
lgtm private def succ as "succ-one" (x : int) : int := x + 1
example : succ.name = "succ-one" := rfl
example : succ.docstring = "One more than `x`." := rfl
#guard succ.check {} []

-- The DSL builds ill-typed programs as readily as well-typed ones; checking is still what rejects
-- them.
#guard !({ three with body := [lgtm| 1 + "a"] } : Decl).check {} []
#guard !({ revCons with body := [lgtm| reverse x] } : Decl).check {} []

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

/-- `fun (p : Point) => new Point { x = p.y, y = p.x }` -/
lgtm def swap (p : struct Point) : struct Point :=
  new Point { x = p.y, y = p.x }

-- And what the two commands build together type checks, which is the point of writing it this way.
#guard swap.check { ss := Structs.ofDecls [Point] } []
#guard !swap.check {} []

lgtm def shift (p : struct Point) (d : int) : struct Point :=
  { p with x = p.x + d }

#guard shift.check { ss := Structs.ofDecls [Point] } []

end Tests
