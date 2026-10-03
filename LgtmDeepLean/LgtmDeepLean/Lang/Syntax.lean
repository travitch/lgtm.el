module

public import LgtmDeepLean.Lang.IR
public import LgtmDeepLean.Lang.TypeCheck
meta import LgtmDeepLean.Lang.IR
meta import LgtmDeepLean.Lang.TypeCheck

/-! # Surface syntax for the IR

An `Expression` written out of its constructors stops being readable at about three nodes:
`.lcons (.stringLit "!") (.lcons (.varRef "s") (.lnil .string))` is a two-element list.  This module
adds notation for `Ty`, `Expression`, and `FuncDecl` so the same programs can be written the way the
docstrings elsewhere already describe them — `fun (x : int) => x + 1`, `g(x)`, `x :: xs`.

Four entry points:

* `[lgtm_ty| (int) -> string]` elaborates to a `Ty`.
* `[lgtm| fun (x : int) => x + 1]` elaborates to an `Expression`.
* `lgtm def` is a command that declares a `FuncDecl`.
* `lgtm struct` is a command that declares a `StructDecl`.
* `lgtm inductive` is a command that declares an `InductiveDecl`.

Everything is a macro, so these expand to ordinary constructor applications and cost nothing at
run time.  A DSL term is *not* checked by `Expression.infer` when it elaborates — `[lgtm| 1 + "a"]`
is a perfectly good `Expression` that happens to be ill typed.  Type checking stays where it was,
in `Expression.check` and `FuncDecl.check`.

Scoping is the IR's, not Lean's: an identifier always becomes a `varRef` of its own name, so the
`x` in `[lgtm| fun (x : int) => x]` refers to the DSL binder and never to a Lean variable called
`x`.  To reach a Lean term of type `Expression` or `Ty`, splice it with `~(...)`.

The keywords inside a DSL term — `bool`, `int`, `string`, `list`, `true`, `false`, `reverse`, `var`,
`struct`, `new`, and `as` — are declared with `&`, Lean's non-reserved symbol form, so importing this
module does not stop `int` or `true` from being used as ordinary Lean identifiers.  What it does cost
is those names as *DSL variables*: the categories below are declared `behavior := symbol`, so an
identifier matching one of them is that keyword and never a `varRef`, and `var "true"` is how a
variable of such a name is reached.  `lgtm` is the one exception and
*is* a reserved token: a command's leading keyword has to be reserved for the command parser to find
it at all, so a file importing this module cannot also name something `lgtm`.

`let`, `in`, `with`, `match`, `inductive`, `if`, `then` and `else` are written as plain symbols rather
than with `&`, because Lean reserves all of them already: declaring them here takes nothing away that
was available before, and a reserved word is not an identifier, so `&` would not match it in the first
place.
-/

/-! `behavior := symbol` is what lets the keywords be non-reserved: it tells the category to consider
its symbol parsers when it meets an identifier, which is how `&"int"` gets a chance to match at all.
Without it a category ignores `&`-declared alternatives entirely. -/

declare_syntax_cat lgtmTy (behavior := symbol)
declare_syntax_cat lgtmExpr (behavior := symbol)

/-! ## Types

`Ty.fn` records every parameter at once, so a function type is written with its parameters in one
comma-separated group: `(int, string) -> int`, and `() -> int` for a function of no arguments. -/

syntax:max &"bool" : lgtmTy
syntax:max &"int" : lgtmTy
syntax:max &"string" : lgtmTy
syntax:max &"list" lgtmTy:max : lgtmTy
/-- `struct Point` is the type the `lgtm struct` named `Point` declares.  The string form,
`struct "my-struct"`, is for struct names that are not Lean identifiers — the same escape hatch
`var` is for variables. -/
syntax:max &"struct" ident : lgtmTy
syntax:max &"struct" str : lgtmTy
/-- `inductive Color` is the type the `lgtm inductive` named `Color` declares, with the same string
escape hatch `struct` has. -/
syntax:max "inductive " ident : lgtmTy
syntax:max "inductive " str : lgtmTy
syntax:max "(" lgtmTy ")" : lgtmTy
syntax:20 "(" lgtmTy,* ")" " -> " lgtmTy:20 : lgtmTy
syntax:max "~" "(" term ")" : lgtmTy

/-- `[lgtm_ty| t]` is the `Ty` that `t` denotes. -/
syntax:max "[lgtm_ty| " lgtmTy "]" : term

macro_rules
  | `([lgtm_ty| bool]) => `(Ty.bool)
  | `([lgtm_ty| int]) => `(Ty.int)
  | `([lgtm_ty| string]) => `(Ty.string)
  | `([lgtm_ty| list $t]) => `(Ty.list [lgtm_ty| $t])
  | `([lgtm_ty| struct $n:ident]) => `(Ty.struct $(Lean.quote n.getId.toString))
  | `([lgtm_ty| struct $n:str]) => `(Ty.struct $n)
  | `([lgtm_ty| inductive $n:ident]) => `(Ty.ind $(Lean.quote n.getId.toString))
  | `([lgtm_ty| inductive $n:str]) => `(Ty.ind $n)
  | `([lgtm_ty| ($t)]) => `([lgtm_ty| $t])
  | `([lgtm_ty| ($ts,*) -> $r]) => do
      let ps ← ts.getElems.mapM fun t => `([lgtm_ty| $t])
      `(Ty.fn [$ps,*] [lgtm_ty| $r])
  | `([lgtm_ty| ~($t)]) => `(($t : Ty))

/-! ## Expressions

Precedence runs `==` looser than `::`, which is looser than `+`/`-`, which are looser than
application and `reverse`, so `1 + 2 :: xs` is `(1 + 2) :: xs`, `f(x) + 1` is `(f(x)) + 1`, and
`x :: xs == ys` compares two lists rather than consing onto a comparison.

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
/-- `true` and `false` are the two `bool` literals.  They are keywords rather than identifiers, so
neither is available as a variable name inside a DSL term; `var "true"` is the escape hatch, the same
one `reverse` and `new` leave. -/
syntax:max &"true" : lgtmExpr
syntax:max &"false" : lgtmExpr
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
/-- `new Color.Rgb(255, 0, 0)` applies the constructor `Rgb` of the inductive type `Color`, and
`new Color.Red()` one that takes nothing — the parentheses are always there, as they are for a call.

The type and the constructor are one dotted identifier because that is how the two are written
everywhere else, and because it is one token as far as Lean's tokenizer is concerned.  Exactly two
components are expected; `new "my-type" "Red"(1)` is the escape hatch for names that are not Lean
identifiers. -/
syntax:max &"new" ident "(" lgtmExpr,* ")" : lgtmExpr
syntax:max &"new" str str "(" lgtmExpr,* ")" : lgtmExpr
/-- One alternative of a `match`: the constructor's name, the names to bind the values it carries to,
and the expression to evaluate when the value was built by it.  A constructor that carries nothing
takes no parentheses. -/
public syntax lgtmAlt := " | " ident ("(" ident,* ")")? " => " lgtmExpr
/-- `match c with | Red => 0 | Rgb(r, g, b) => r` takes a value of an inductive type apart.

The alternatives have to be the type's constructors in the order it declares them, which is the type
checker's business rather than the parser's.  An alternative's expression extends as far right as it
can, so a `match` nested inside one needs parentheses — the same way a `let` does. -/
syntax:10 "match " lgtmExpr " with" lgtmAlt* : lgtmExpr
/-- `if b then { 1 } else { 2 }` chooses between its two branches.

The branches are braced, so the form ends where the last `}` does and needs no parentheses to be an
operand: `if b then { 1 } else { 2 } + 1` adds to the conditional rather than to its second branch,
which is the opposite of how a `let` or a `match` alternative reads.  The condition takes no braces
because `then` is what ends it.

Both branches must have the same type and the condition must be a `bool`, which is the type checker's
business rather than the parser's. -/
syntax:max "if " lgtmExpr " then " "{" lgtmExpr "}" " else " "{" lgtmExpr "}" : lgtmExpr
syntax:65 lgtmExpr:65 " + " lgtmExpr:66 : lgtmExpr
syntax:65 lgtmExpr:65 " - " lgtmExpr:66 : lgtmExpr
syntax:55 lgtmExpr:56 " :: " lgtmExpr:55 : lgtmExpr
/-- `a == b` compares two values structurally, however deep they are.

It is the loosest of the operators, so `x + 1 == y` and `x :: xs == ys` need no parentheses, and it
is non-associative: `a == b == c` is a parse error rather than one of the two comparisons it could
have meant.  A comparison *of* comparisons is written with the parentheses that say which, since what
one produces is an ordinary `bool`.

The operands must have the same type, and it must be a type a comparison can reach the bottom of —
which is the type checker's business rather than the parser's. -/
syntax:50 lgtmExpr:51 " == " lgtmExpr:51 : lgtmExpr
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
  | `([lgtm| true]) => `(Expression.boolLit true)
  | `([lgtm| false]) => `(Expression.boolLit false)
  | `([lgtm| $n:num]) => `(Expression.intLit $n)
  | `([lgtm| $s:str]) => `(Expression.stringLit $s)
  | `([lgtm| ($e)]) => `([lgtm| $e])
  | `([lgtm| ~($e)]) => `(($e : Expression))
  | `([lgtm| $a + $b]) => `(Expression.plus [lgtm| $a] [lgtm| $b])
  | `([lgtm| $a - $b]) => `(Expression.minus [lgtm| $a] [lgtm| $b])
  | `([lgtm| $a :: $b]) => `(Expression.lcons [lgtm| $a] [lgtm| $b])
  | `([lgtm| $a == $b]) => `(Expression.equals [lgtm| $a] [lgtm| $b])
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
  | `([lgtm| if $c then { $thn } else { $els }]) =>
      `(Expression.ite [lgtm| $c] [lgtm| $thn] [lgtm| $els])
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
  | `([lgtm| new $n:ident($args,*)]) => do
      match n.getId.toString.splitOn "." with
      | [ty, c] =>
          let as ← args.getElems.mapM fun a => `([lgtm| $a])
          `(Expression.indNew $(Lean.quote ty) $(Lean.quote c) [$as,*])
      | _ =>
          Lean.Macro.throwErrorAt n
            "a constructor is written `new Type.Ctor(...)`, with the type and the constructor it \
             belongs to"
  | `([lgtm| new $ty:str $c:str($args,*)]) => do
      let as ← args.getElems.mapM fun a => `([lgtm| $a])
      `(Expression.indNew $ty $c [$as,*])
  | `([lgtm| match $e with $alts:lgtmAlt*]) => do
      let as ← alts.mapM fun alt =>
        match alt with
        | `(lgtmAlt| | $c:ident $[($xs:ident,*)]? => $b:lgtmExpr) => do
            let ns : Array (Lean.TSyntax `term) :=
              ((xs.map (·.getElems)).getD #[]).map fun x => Lean.quote x.getId.toString
            `(($(Lean.quote c.getId.toString), [$ns,*], [lgtm| $b]))
        | _ => Lean.Macro.throwUnsupported
      `(Expression.indMatch [lgtm| $e] [$as,*])

/-! ## Declarations -/

/-- The visibility of a `lgtm def`.  `public` because a `module` hides even the names of its own
parser aliases otherwise, and this one is referred to by the command syntax below. -/
public syntax lgtmVis := "private "

/-- `lgtm def f (x : int) : int := body` declares `f : FuncDecl`.

The IR name defaults to the Lean name; `as "f-name"` overrides it, which is what IR names that are
not Lean identifiers need.  A doc comment becomes the `FuncDecl.docstring` field as well as the Lean
declaration's own documentation.

The parameters are the `FuncDecl`'s parameter list and so are also the context its body is checked
in; they are not Lean binders.

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
                    resultType := [lgtm_ty| $rt] : FuncDecl })
      match vis with
      | some _ => `($[$doc:docComment]? private def $n : FuncDecl := $val)
      | none => `($[$doc:docComment]? def $n : FuncDecl := $val)

/-- Fail at the first of `ns` that repeats a name an earlier one already used, saying so in terms of
`what` — "field", "constructor".

`StructDecl.fields` and `InductiveDecl.constructors` are both association lists read with
`List.lookup`, so an entry repeating a name is one nothing can reach: `StructDecl.FieldNamesUnique`
and `InductiveDecl.CtorNamesUnique` are the conditions saying so, and `Program.check` rejects a
declaration failing either.  Failing here as well is what keeps the surface syntax from writing one
at all, and it is the better place to say it: the error lands on the name that repeats rather than
on the program the declaration ends up in.

`meta` because it runs while a macro expands rather than at run time, and `public` for the reason
`lgtmVis` is: a `module` hides even the names its own macros expand to. -/
public meta def throwOnRepeatedName (what : String) (ns : Array Lean.Ident) :
    Lean.MacroM Unit := do
  let mut seen : Array String := #[]
  for n in ns do
    let s := n.getId.toString
    if seen.contains s then
      Lean.Macro.throwErrorAt n s!"duplicate {what} `{s}`: a declaration names each {what} once"
    seen := seen.push s

/-- `lgtm struct Point { x : int, y : int }` declares `Point : StructDecl`.

The same shape as `lgtm def`: the IR name defaults to the Lean name and `as "point"` overrides it,
and `lgtm private struct` makes the generated Lean declaration `private`.  The fields are in the
order they are written, which is the order a `new` has to give them in.

No two fields may share a name, which `StructDecl.FieldNamesUnique` is the condition for: a second
`x` is a field no `p.x` could read and no `{ p with x = ... }` could rebind, so it is an error here
rather than a declaration only `Program.check` would turn down.

A doc comment documents the Lean declaration only.  A `StructDecl` has no docstring field to put it
in, unlike a `FuncDecl`. -/
syntax (docComment)? "lgtm " (lgtmVis)? &"struct" ident (&"as" str)?
  "{" (ident " : " lgtmTy),* "}" : command

macro_rules
  | `($[$doc:docComment]? lgtm $[$vis:lgtmVis]? struct $n:ident $[as $ir:str]?
        { $[$fs:ident : $ts:lgtmTy],* }) => do
      throwOnRepeatedName "field" fs
      let fields ← (fs.zip ts).mapM fun (f, t) =>
        `(($(Lean.quote f.getId.toString), [lgtm_ty| $t]))
      let irName := ir.getD (Lean.quote n.getId.toString)
      let val ← `({ name := $irName, fields := [$fields,*] : StructDecl })
      match vis with
      | some _ => `($[$doc:docComment]? private def $n : StructDecl := $val)
      | none => `($[$doc:docComment]? def $n : StructDecl := $val)

/-- One constructor of a `lgtm inductive`: its name, and the types of the data it carries.  A
constructor that carries nothing takes no parentheses, which is what makes a plain enumeration look
like one. -/
public syntax lgtmCtor := ident ("(" lgtmTy,* ")")?

/-- `lgtm inductive Color { Red, Green, Rgb(int, int, int) }` declares `Color : InductiveDecl`.

The same shape as `lgtm struct`: the IR name defaults to the Lean name and `as "color"` overrides it,
and `lgtm private inductive` makes the generated Lean declaration `private`.  The constructors are in
the order they are written, which is the order a `match` has to give its alternatives in.

A constructor's data has types but no names — it is taken apart by position — so a constructor is
written like a function type's parameter list rather than like a struct's fields.

No two constructors may share a name, which `InductiveDecl.CtorNamesUnique` is the condition for and
which is an error here for the reason a repeated field is: a second `Red` is one `new C.Red(...)`
could never build and one a `match` would have to write a second alternative for and never reach.

A doc comment documents the Lean declaration only.  An `InductiveDecl` has no docstring field to put
it in, as a `StructDecl` has not. -/
syntax (docComment)? "lgtm " (lgtmVis)? "inductive " ident (&"as" str)?
  "{" lgtmCtor,* "}" : command

macro_rules
  | `($[$doc:docComment]? lgtm $[$vis:lgtmVis]? inductive $n:ident $[as $ir:str]?
        { $cs:lgtmCtor,* }) => do
      let ctors ← cs.getElems.mapM fun c =>
        match c with
        | `(lgtmCtor| $cn:ident $[($ts:lgtmTy,*)]?) => do
            let tys ← ((ts.map (·.getElems)).getD #[]).mapM fun t => `([lgtm_ty| $t])
            return (cn, ← `(($(Lean.quote cn.getId.toString), [$tys,*])))
        | _ => Lean.Macro.throwUnsupported
      throwOnRepeatedName "constructor" (ctors.map Prod.fst)
      let cs := ctors.map Prod.snd
      let irName := ir.getD (Lean.quote n.getId.toString)
      let val ← `({ name := $irName, constructors := [$cs,*] : InductiveDecl })
      match vis with
      | some _ => `($[$doc:docComment]? private def $n : InductiveDecl := $val)
      | none => `($[$doc:docComment]? def $n : InductiveDecl := $val)

section Tests

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

end Tests
