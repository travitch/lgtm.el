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

The keywords inside a DSL term — `bool`, `int`, `string`, `list`, `option`, `true`, `false`, `some`,
`none`, `reverse`, `var`, `struct`, `new`, and `as` — are declared with `&`, Lean's non-reserved
symbol form, so importing this module does not stop `int` or `some` from being used as ordinary Lean
identifiers.  What it does cost is those names as *DSL variables*: the categories below are
declared `behavior := symbol`, so an identifier matching one of them is that keyword and never a
`varRef`, and `var "true"` is how a variable of such a name is reached.  `lgtm` is the one exception
and *is* a reserved token: a command's leading keyword has to be reserved for the command parser to
find it at all, so a file importing this module cannot also name something `lgtm`.

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
/-- `option int` is a value of type `int` or nothing.

Like `list` and unlike `struct` and `inductive`, it carries the type it holds rather than naming a
declaration, so there is no `lgtm` command declaring one and no `TypeDecls` entry to resolve. -/
syntax:max &"option" lgtmTy:max : lgtmTy
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
  | `([lgtm_ty| option $t]) => `(Ty.option [lgtm_ty| $t])
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

The two option values are written `some(1)` and `none : int`, and a `match` whose alternatives are
named `none` and `some` takes one apart.  The empty one carries a type for the reason an empty list
literal does — it holds nothing to read one off — while `some` needs none, since what it holds says
it.

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
/-- `some(e)` is the option holding `e`.  It takes no annotation, because `optionSome` takes none:
the value it holds is what the element type is read off.

Written with parentheses the way a call and a `new` are, and for the same reason the `match`
alternative `| some(x) => ...` is: the one value an option holds is given like the one argument a
constructor takes. -/
syntax:max &"some" "(" lgtmExpr ")" : lgtmExpr
/-- `none : int` is the empty option at `int`, annotated because `optionNone` is: an empty option
holds nothing to read a type off, exactly as an empty list literal does not.

The annotation is a type at `max`, so `none : list int` and `none : option int` need no parentheses
while a function type does: `none : ((int) -> int)`.  Inside a list literal, which ends with an
annotation of its own, the option takes parentheses to say which `:` is which:
`[(none : int) : option int]`.

`none` is a keyword, so neither it nor `some` is available as a variable name inside a DSL term;
`var "none"` is the escape hatch, the same one `true` and `new` leave. -/
syntax:max &"none" " : " lgtmTy:max : lgtmExpr
/-- One alternative of a `match`: the constructor's name, the names to bind the values it carries to,
and the expression to evaluate when the value was built by it.  A constructor that carries nothing
takes no parentheses. -/
public syntax lgtmAlt := " | " ident ("(" ident,* ")")? " => " lgtmExpr
/-- `match c with | Red => 0 | Rgb(r, g, b) => r` takes a value of an inductive type apart.

The alternatives have to be the type's constructors in the order it declares them, which is the type
checker's business rather than the parser's.  An alternative's expression extends as far right as it
can, so a `match` nested inside one needs parentheses — the same way a `let` does.

`match o with | none => 0 | some(x) => x` is the one special case: alternatives named `none` and
`some` make an `optionMatch` rather than an `indMatch`, since an option is taken apart by a form of
its own.  The two have to be both of them and in that order, which the parser does not ask of the
alternatives of an `indMatch` but which `optionMatch` asks here — it holds the two cases an option
has rather than a list to check against a declaration, so there is nothing for a third alternative
or a missing one to mean.  The cost is that an inductive type declaring a constructor called `none`
or `some` is one this syntax cannot match on; `~(Expression.indMatch ...)` is the way to write that
one. -/
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

/-- The `optionMatch` on `scrut` that `alts` describes, when they are the option forms:
`| none => e` first and `| some(x) => e` second, each alternative given as its constructor name, the
names it binds, and its body.

`none` when no alternative names either, which is every other `match` and is an `indMatch`; an error
when one does and the rest of the shape is not an option's, because there is no second reading to
fall back on — a `match` mentioning `none` is one the writer meant for an option.

`meta` because it runs while a macro expands, and `public` for the reason `throwOnRepeatedName` is:
a `module` hides even the names its own macros expand to. -/
public meta def optionMatchAlts (scrut : Lean.TSyntax `lgtmExpr)
    (alts : Array (Lean.Ident × Array Lean.Ident × Lean.TSyntax `lgtmExpr)) :
    Lean.MacroM (Option (Lean.TSyntax `term)) := do
  let isOptionCtor (c : Lean.Ident) : Bool := c.getId == `none || c.getId == `some
  let some (named, _, _) := alts.find? (fun (c, _, _) => isOptionCtor c) | return none
  let #[(nc, nxs, nbody), (sc, sxs, sbody)] := alts
    | Lean.Macro.throwErrorAt named
        "a match on an option has two alternatives: `| none => ... | some(x) => ...`"
  unless nc.getId == `none && sc.getId == `some do
    Lean.Macro.throwErrorAt named
      "a match on an option takes `none` first and `some` second"
  unless nxs.isEmpty do
    Lean.Macro.throwErrorAt nc "`none` holds nothing, so its alternative binds no names"
  let #[x] := sxs
    | Lean.Macro.throwErrorAt sc
        "`some` holds one value, so its alternative binds one name: `| some(x) => ...`"
  return some (← `(Expression.optionMatch [lgtm| $scrut] [lgtm| $nbody]
    $(Lean.quote x.getId.toString) [lgtm| $sbody]))

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
  | `([lgtm| some($e)]) => `(Expression.optionSome [lgtm| $e])
  | `([lgtm| none : $t]) => `(Expression.optionNone [lgtm_ty| $t])
  | `([lgtm| match $e with $alts:lgtmAlt*]) => do
      let parsed ← alts.mapM fun alt =>
        match alt with
        | `(lgtmAlt| | $c:ident $[($xs:ident,*)]? => $b:lgtmExpr) =>
            return (c, (xs.map (·.getElems)).getD #[], b)
        | _ => Lean.Macro.throwUnsupported
      -- An alternative named `none` or `some` is a match on an option rather than on a declared
      -- inductive type, and is the one form taking it apart.
      if let some m ← optionMatchAlts e parsed then
        return m
      let as ← parsed.mapM fun (c, xs, b) => do
        let ns : Array (Lean.TSyntax `term) := xs.map fun x => Lean.quote x.getId.toString
        `(($(Lean.quote c.getId.toString), [$ns,*], [lgtm| $b]))
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

