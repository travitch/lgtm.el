module

public import LgtmDeepLean.Lang.IR
public import LgtmDeepLean.Lang.TypeCheck
meta import LgtmDeepLean.Lang.IR
meta import LgtmDeepLean.Lang.TypeCheck
public meta import LgtmDeepLean.Lang.IR.ToExpr
public meta import LgtmDeepLean.Lang.Syntax.Scope

/-! # Surface syntax for the IR

An `Expression` written out of its constructors stops being readable at about three nodes:
`.lcons (.stringLit "!") (.lcons (.varRef "s") (.lnil .string))` is a two-element list.  This module
adds notation for `Ty`, `Expression`, and `FuncDecl` so the same programs can be written the way the
docstrings elsewhere already describe them — `fun (x : int) => x + 1`, `g(x)`, `x :: xs`.

Five entry points:

* `[lgtm_ty| (int) -> string]` elaborates to a `Ty`.
* `[lgtm| fun (x : int) => x + 1]` elaborates to an `Expression`.
* `@[lgtm] def` is a command that declares a `FuncDecl`.
* `@[lgtm] structure` is a command that declares a `StructDecl`.
* `@[lgtm] inductive` is a command that declares an `InductiveDecl`.
* `@[lgtm, forward] def` is a command that declares a signature and nothing else, for two
  declarations that call each other.

The four commands are spelled the way the Lean declaration each of them generates is: an attribute,
then `def`, `structure` or `inductive`, with a `structure`'s fields and an `inductive`'s
constructors one to a line under a `where`.  They are not Lean's declarations — the signature and
the body are the DSL's, and `(x : int)` is a `FuncDecl` parameter rather than a Lean binder — but
the text is shaped like Lean's, which is what lets a tool that reads Lean by its grammar rather than
by its parser get through a file of them.

`[lgtm_body| ...]` is one more and is not for writing by hand: `@[lgtm] def` generates it as the value
of the Lean declaration it makes, because the body has to be read under the declaration's own
context rather than as a fragment.  See "What the commands do besides declare".

What a DSL term elaborates to is an ordinary constructor application and costs nothing at run time,
the way it did when all of this was a macro.  What is no longer the same is when it is checked.

A *term* is still not checked: `[lgtm| 1 + "a"]` is a perfectly good `Expression` that happens to be
ill typed, and `[lgtm| x + 1]` mentions an `x` that nothing need have bound, because a fragment has
no context for either to be wrong in.

A *declaration* is checked by the command that makes it, against the declarations in scope at that
point, and what the check finds is reported on the part of the declaration that has it — the token
of a name nothing declares, the innermost subexpression that does not type check.  That is what the
elaborators below are for: they read a form into the value it denotes rather than into syntax for
that value, so one pass holds the declaration and the syntax every part of it came from.
`Program.check` is still the authority and still what `LgtmDeepLean.Model.Tests` runs; see the
"What the commands do besides declare" section below for what the two see differently.

Scoping is the IR's, not Lean's: an identifier becomes a `varRef` of its own name, so the `x` in
`[lgtm| fun (x : int) => x]` refers to the DSL binder and never to a Lean variable called `x`.  To
reach a Lean term of type `Expression` or `Ty`, splice it with `~(...)`.

Nothing about a DSL term is decided by what Lean names are in scope.  A *dotted* identifier is
either one IR name or a field read, and which one it is cannot be read off the syntax: `Foo.bar` is
the IR name `Foo.bar` when an `lgtm` command has declared that IR name, and otherwise the variable
`Foo` with its field `bar` read.  What is consulted is the IR names an ordinary `import` brings in
(`LgtmDeepLean.Lang.Syntax.Scope`), where it used to be the Lean names a `meta import` brought in —
so a module calling another's declarations no longer needs to import it twice.

The keywords inside a DSL term — `bool`, `int`, `string`, `list`, `option`, `except`, `hashmap`,
`tuple`,
`true`, `false`, `some`, `none`, `ok`, `error`, `min`, `max`, `reverse`, `length`, `map`, `flatMap`,
`findIndex`,
`sortOn`, `sortBy`,
`toList`,
`unreachable`, `var`,
`struct`, `new`, and
`as` — are declared
with `&`, Lean's
non-reserved symbol form, so importing this module does not stop `int` or `some` from being used as
ordinary Lean identifiers.  What it does cost is those names as *DSL variables*: the categories
below are declared `behavior := symbol`, so an identifier matching one of them is that keyword and
never a `varRef`, and `var "true"` is how a variable of such a name is reached.  `lgtm` itself costs
nothing either: the commands below lead with `@[lgtm]`, which is one token of its own, and the
`forward` form spells both of its words with `&`, so a file importing this module may still name
something `lgtm`.

`let`, `with`, `match`, `inductive`, `if`, `then` and `else` are written as plain symbols rather
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

syntax :max &"bool" : lgtmTy

syntax :max &"int" : lgtmTy

syntax :max &"string" : lgtmTy

syntax :max &"list" lgtmTy:max : lgtmTy

/-- `option int` is a value of type `int` or nothing.

Like `list` and unlike `struct` and `inductive`, it carries the type it holds rather than naming a
declaration, so there is no `lgtm` command declaring one and no `TypeDecls` entry to resolve. -/
syntax :max &"option" lgtmTy:max : lgtmTy

/-- `except string int` is an `int`, or a `string` instead of one: the error type first and the
payload second, the order `Except ε α` relates them in.

Both halves are at `max` and are read in order, the way `hashmap`'s two are, so
`except string list int` is an except of a list and `except list string int` one whose errors are
lists, while a function type on either side takes parentheses: `except string ((int) -> int)`.

Like `list`, `option` and `hashmap` it carries the types it relates, so there is no `lgtm` command
declaring one and no `TypeDecls` entry to resolve. -/
syntax :max &"except" lgtmTy:max lgtmTy:max : lgtmTy

/-- `hashmap string int` is a finite map from `string` keys to `int` values.

Like `list` and `option` and unlike `struct` and `inductive`, it carries the types it relates rather
than naming a declaration, so there is no `lgtm` command declaring one and no `TypeDecls` entry to
resolve.

Both halves are at `max` and are read in order, so `hashmap string list int` is a map to lists and
`hashmap list string int` a map from them, while a function type on either side takes parentheses:
`hashmap string ((int) -> int)`. -/
syntax :max &"hashmap" lgtmTy:max lgtmTy:max : lgtmTy

/-- `tuple(int, string)` is an `int` beside a `string`: as many values as the types it lists, each at
the type in its position.

Written with its types in one comma-separated group in parentheses, the way a function type's
parameters are and unlike `hashmap`'s two: a tuple takes any number of them, so where the group ends
is what says how many there are, and a function type on any of them needs no parentheses of its own.
`tuple()` is the empty tuple type.

Like `list`, `option` and `hashmap`, and unlike `struct` and `inductive`, it carries the types it
relates rather than naming a declaration, so there is no `lgtm` command declaring one and no
`TypeDecls` entry to resolve. -/
syntax :max &"tuple" "(" lgtmTy,* ")" : lgtmTy

/-- `struct Point` is the type the `@[lgtm] structure` named `Point` declares.  The string form,
`struct "my-struct"`, is for struct names that are not Lean identifiers — the same escape hatch
`var` is for variables. -/
syntax :max &"struct" ident : lgtmTy

syntax :max &"struct" str : lgtmTy

/-- `inductive Color` is the type the `@[lgtm] inductive` named `Color` declares, with the same
string escape hatch `struct` has. -/
syntax :max "inductive " ident : lgtmTy

syntax :max "inductive " str : lgtmTy

syntax :max "(" lgtmTy ")" : lgtmTy

syntax :20 "(" lgtmTy,* ")" " -> " lgtmTy:20 : lgtmTy

syntax :max "~" "(" term ")" : lgtmTy

/-- `[lgtm_ty| t]` is the `Ty` that `t` denotes. -/
syntax :max "[lgtm_ty| " lgtmTy "]" : term

/-! ## Elaborating a DSL term

A form is read into the value it denotes — a `Ty`, an `Expression` — rather than into syntax for
that value, and the Lean term the quotation becomes is recovered from the value with `ToExpr`
(`LgtmDeepLean.Lang.IR.ToExpr`).  What that buys is the one thing a macro cannot have: a pass
holding the value *and* the syntax it came from at once, which is what lets the `lgtm` commands
check the declaration they are elaborating and report what they find where the writer can see it.

The cost is that a splice stops being transparent.  `~(e)` is a *Lean* term, so a pass building
values cannot read a value out of it — in `[lgtm| ~(f x)]` there need not be one yet, and
`Eval/Tests.lean` splices expressions that are free variables of the theorem around them.  A splice
is therefore elaborated to an `Expr` and left standing in the value as a marked variable, which
`plugSplices` puts back when the value becomes a term.  What the marker costs is the checking: a
value with one in it is not the expression the writer wrote, so a declaration containing a splice is
left to `Program.check`, which sees it after Lean has evaluated it. -/

open Lean

/-- The reserved prefix of the variable a spliced term stands as while a DSL term is being built.

A name beginning with it is one `plugSplices` would rewrite, which is what spells `var "~splice#0"`
and `struct "~splice#0"` out of the language.  Neither is reachable by accident: `~` starts no Lean
identifier, so writing one takes the string escape hatch deliberately. -/
meta def spliceMarker : String := "~splice#"

/-- The variable the `i`th splice of a term stands as. -/
meta def spliceVar (i : Nat) : String := s!"{spliceMarker}{i}"

/-- The index of the splice `s` marks, if it marks one. -/
private meta def spliceIndex? (s : String) : Option Nat :=
  if s.startsWith spliceMarker then (s.drop spliceMarker.length).toNat? else none

/-- `e` with every splice marker in it replaced by the term that splice elaborated to.

Done on the `Expr` rather than on the value: a marker is a `varRef` or a `struct` of a reserved
name, so `toExpr` turns it into a term of exactly one shape, and recognising that shape is a
traversal of ten lines where recognising it in the value would be one case per form of the IR. -/
meta def plugSplices (splices : Array Expr) (e : Expr) : Expr :=
  if splices.isEmpty then e
  else
    e.replace fun sub =>
      match sub with
      | .app (.const c _) (.lit (.strVal s)) =>
          if c == ``Expression.varRef || c == ``Ty.struct then
            (spliceIndex? s).bind fun i => splices[i]?
          else
            none
      | _ => none

/-- How far reading a DSL term has got: where its splices went, and whether anything has been
reported about it.

`reported` is what keeps one mistake from being described twice.  A name nothing declares is also a
name the type checker can say nothing useful about — it would report the same mistake a second time,
one form further out — so a term that has had something said about it is not then checked. -/
meta structure LgtmElabState where
  splices : Array Expr := #[]
  reported : Bool := false
  /-- Every expression the term was built from, each with the syntax it was written as and the
  context it stands in, in the order they were finished — so a child comes before its parent, and
  the first entry that does not type check is the innermost one that does not.

  Recorded only for a declaration, since a fragment is not checked.  What it is for is saying
  *where*: `Expression.inferE` reports the innermost thing it could not do but not which part of
  the source that was, and this is how the two are put back together. -/
  nodes : Array (Syntax × Expression × Context) := #[]

/-- What a DSL term is read against: the declarations in scope, and whether to report a name that
nothing in scope declares.

Names are resolved either way — which of the two things a dotted identifier means depends on it —
but reported only for a declaration.  A bare `[lgtm| ...]` is a fragment and may mention anything:
`[lgtm| x + 1]` is the expression it says, and has no context in which `x` could be wrong.  A
declaration is the opposite: its parameters and the globals are the whole of what its body may
mention, so a name outside them is a mistake and the commands ask to hear about it. -/
meta structure LgtmElabCtx where
  scope : LgtmScope
  /-- What the term may mention besides what is in scope: the declaration being elaborated, so that
  its body may call itself and a struct may have a field of its own type.

  A declaration's signature is read before its body and a type name before the fields under it, so
  a provisional entry carrying as much of the declaration as has been read is enough — which is all
  a mention of it needs, since what a caller reads is the signature. -/
  extra : LgtmScope := {}
  report : Bool

/-- The globals a term may call: those in scope, and the declaration being elaborated. -/
meta def LgtmElabCtx.allGlobals (ctx : LgtmElabCtx) : Globals := ctx.scope.globals ++ ctx.extra.globals

/-- The structs a term may name, the same way. -/
meta def LgtmElabCtx.allStructs (ctx : LgtmElabCtx) : Structs := ctx.scope.structs ++ ctx.extra.structs

/-- The inductive types a term may name, the same way. -/
meta def LgtmElabCtx.allInductives (ctx : LgtmElabCtx) : Inductives :=
  ctx.scope.inductives ++ ctx.extra.inductives

/-- The type declarations a term is read and checked against. -/
meta def LgtmElabCtx.allTypeDecls (ctx : LgtmElabCtx) : TypeDecls where
  ss := ctx.allStructs
  is := ctx.allInductives

/-- The monad a DSL term is read in: `TermElabM` because a splice is a Lean term and has to be
elaborated, with the scope to resolve names against and the splices met so far. -/
meta abbrev LgtmElabM :=
  ReaderT LgtmElabCtx (StateRefT LgtmElabState Elab.TermElabM)

/-- Point `ref` at the Lean declaration that `irName`'s `lgtm` command generated, so that the
editor can follow a mention of an IR name to where it was declared.

What this records is the node an identifier's elaboration would have left had the name been a Lean
one: goto-definition and hover both read it, so a call inside a DSL body becomes navigable and
shows the declaration's docstring, for the cost of a lookup the name resolution has already done.

Silent when the name is one no command declared — a parameter, a `let` — since there is no
declaration for it to point at. -/
private meta def addIrNameInfo (ref : Syntax) (irName : String) : LgtmElabM Unit := do
  let ctx ← read
  let some entry := (ctx.extra.find? irName).orElse fun _ => ctx.scope.find? irName | return
  if (← getEnv).contains entry.leanName then
    Elab.addConstInfo ref entry.leanName

/-- Record that the source `ref` was written at the DSL type `t`, so that hovering over it shows the
type.

A `DelabTermInfo` rather than a `TermInfo`, because its `mkDocString?` is the one place in an info
node arbitrary text can be put: what a `TermInfo` hover shows is the *Lean* type of a Lean
expression, and the type of a DSL expression is a `Ty` rather than a Lean type at all — the value
`toExpr t` has the Lean type `Ty` however interesting the `Ty` is.  `expr` is still filled in with
the type as a value, since hover is not the only thing that reads an info node.

Pushed for a declaration only, and so only where a type is known: a fragment is not checked, and
nothing is recorded about an expression `Expression.inferE` could say nothing about. -/
meta def addTyInfo (ref : Syntax) (t : Ty) : Elab.TermElabM Unit := do
  -- The documentation of the form `ref` is written as, which is what the editor showed over it
  -- before there was a type to show: the hover of an info node replaces the one the parser's
  -- docstring would have given, so the type is put above it rather than in place of it.
  let formDoc? ← findDocString? (← getEnv) ref.getKind
  let text := s!"```lgtm\n{t.render}\n```" ++ (formDoc?.map (s!"\n***\n" ++ ·)).getD ""
  Elab.pushInfoLeaf <| .ofDelabTermInfo {
    elaborator := `LgtmDeepLean.tyInfo
    stx := ref
    lctx := .empty
    expectedType? := none
    expr := toExpr t
    mkDocString? := some fun _ => return text
  }

/-- The type a binder is recorded at when what it binds has none: a `let` whose bound expression is
ill typed, or a `match` on something that is not of the kind being taken apart.

Only the recording is affected, never the checking.  Whatever had no type is itself a node that
does not type check and was finished first, so it is what gets reported, and nothing is ever said
about a binder standing at this. -/
meta def unknownTy : Ty := .tuple []

/-- Report `message` at `ref`, unless this term is a fragment nothing is reported about. -/
private meta def reportAt (ref : Syntax) (message : String) : LgtmElabM Unit := do
  if (← read).report then
    logErrorAt ref message
    modify fun s => { s with reported := true }

/-- Elaborate the spliced term `t` at type `ty`, and give back the name of the marker standing for
it. -/
private meta def elabSplice (t : Term) (ty : Name) : LgtmElabM String := do
  let e ← Elab.Term.elabTerm t (mkConst ty)
  let i := (← get).splices.size
  modify fun s => { s with splices := s.splices.push e }
  return spliceVar i

/-- Report at `ref` unless `name` is a struct in scope, saying which of the two kinds it is when it
is the other one. -/
private meta def checkStructName (ref : Syntax) (name : String) : LgtmElabM Unit := do
  let ctx ← read
  if (ctx.allStructs.lookup name).isSome then
    addIrNameInfo ref name
    return
  if (ctx.allInductives.lookup name).isSome then
    reportAt ref s!"'{name}' is an inductive type, not a struct: write `inductive {name}`"
  else
    reportAt ref
      (withSuggestion name (ctx.allStructs.map Prod.fst) s!"no struct named '{name}' is declared")

/-- Report at `ref` unless `name` is an inductive type in scope, the way `checkStructName` does. -/
private meta def checkIndName (ref : Syntax) (name : String) : LgtmElabM Unit := do
  let ctx ← read
  if (ctx.allInductives.lookup name).isSome then
    addIrNameInfo ref name
    return
  if (ctx.allStructs.lookup name).isSome then
    reportAt ref s!"'{name}' is a struct, not an inductive type: write `struct {name}`"
  else
    reportAt ref
      (withSuggestion name (ctx.allInductives.map Prod.fst)
        s!"no inductive named '{name}' is declared")

/-- Build the `Ty` that `stx` denotes. -/
meta partial def elabLgtmTy (stx : TSyntax `lgtmTy) : LgtmElabM Ty := do
  match stx with
  | `(lgtmTy| bool) => return .bool
  | `(lgtmTy| int) => return .int
  | `(lgtmTy| string) => return .string
  | `(lgtmTy| list $t) => return .list (← elabLgtmTy t)
  | `(lgtmTy| option $t) => return .option (← elabLgtmTy t)
  | `(lgtmTy| except $e $t) => return .except (← elabLgtmTy e) (← elabLgtmTy t)
  | `(lgtmTy| hashmap $k $v) => return .hashmap (← elabLgtmTy k) (← elabLgtmTy v)
  | `(lgtmTy| tuple($ts,*)) => return .tuple (← ts.getElems.toList.mapM elabLgtmTy)
  | `(lgtmTy| struct $n:ident) => do
      let name := n.getId.toString
      checkStructName n name
      return .struct name
  | `(lgtmTy| struct $n:str) => do
      checkStructName n n.getString
      return .struct n.getString
  | `(lgtmTy| inductive $n:ident) => do
      let name := n.getId.toString
      checkIndName n name
      return .ind name
  | `(lgtmTy| inductive $n:str) => do
      checkIndName n n.getString
      return .ind n.getString
  | `(lgtmTy| ($t)) => elabLgtmTy t
  | `(lgtmTy| ($ts,*) -> $r) =>
      return .fn (← ts.getElems.toList.mapM elabLgtmTy) (← elabLgtmTy r)
  | `(lgtmTy| ~($t)) => return .struct (← elabSplice t ``Ty)
  | _ => throwErrorAt stx "not a type of the `lgtm` language"

/-- Run `x` against the declarations in scope, and give back what it built together with the state
it left: the splices to plug back in, and whether it reported anything. -/
meta def LgtmElabM.run' (report : Bool) (x : LgtmElabM α) (extra : LgtmScope := {}) :
    Elab.TermElabM (α × LgtmElabState) := do
  let scope ← getLgtmScope
  StateRefT'.run (x.run { scope, extra, report }) {}

/-- The term a DSL value elaborates to: what `ToExpr` makes of it, with the splices put back. -/
meta def lgtmTerm [ToExpr α] (v : α) (st : LgtmElabState) : Expr :=
  plugSplices st.splices (toExpr v)

elab_rules : term
  | `([lgtm_ty| $t]) => do
      let (v, st) : Ty × LgtmElabState ← LgtmElabM.run' (report := false) (elabLgtmTy t)
      return lgtmTerm v st

/-! ## Expressions

Precedence runs `||` looser than `&&`, which is looser than `==`, `<` and `<=`, which are looser
than `::`, which is looser than `+`/`-`, which are looser than application, `reverse` and `length`,
so `1 + 2 :: xs` is `(1 + 2) :: xs`, `f(x) + 1` is `(f(x)) + 1`, `x :: xs == ys` compares two lists
rather than consing onto a comparison, `x < y + 1` compares against the sum, and `x == y && b` is a
conjunction of a comparison rather than a comparison against a conjunction.

The three comparisons share one level and none of them associates, so `a == b == c` and `a < b <= c`
are parse errors rather than one of the two readings each could have had.

`min x y` and `max x y` are the other two `int` operations, prefix keywords rather than operators
because neither has a symbol to be written with.  They bind as tightly as `reverse`, so `min x y + 1`
is the minimum plus one.

A list literal carries its element type, because `lnil` does: `[1, 2 : int]` is
`.lcons (.intLit 1) (.lcons (.intLit 2) (.lnil .int))`, and the empty list is `[: int]`.

The seven prefix list operations are `reverse xs`, `length xs`, `map xs f`, `flatMap xs f`,
`findIndex xs f`, `sortOn xs f` and
`sortBy xs f`, all prefix
keywords binding as tightly as application.  They differ in what comes back out: a reversal and the
two sorts are lists of the same type, a mapping is a list of whatever its function returns, a flat
mapping is the lists its function returns run together, a length is an `int` whatever the elements
were, and a search is an `option int` — the position of the first element its predicate accepts,
and nothing where it accepts none.  A sort takes a function as a mapping does and still
produces a list of the type it was given, because what the function returns is how the elements are
ordered rather than what they become: a key apiece under `sortOn`, and the comparison itself under
`sortBy`.  `map` is also a hashmap's operation, and which of the two a term is is decided by the
type inferred for what is mapped over — see the note on the two forms below.

The eighth is `xs[i]`, an index, which is not a prefix keyword but the brackets a hashmap lookup is
written in: it hands back an `option` of the element type, `none` where the list has no element at
that position, and which of the two readings the brackets have is decided by the type inferred for
what is indexed.

The two option values are written `some(1)` and `none : int`, and a `match` whose alternatives are
named `none` and `some` takes one apart.  The empty one carries a type for the reason an empty list
literal does — it holds nothing to read one off — while `some` needs none, since what it holds says
it.

The two except values are written `ok(1) : string` and `error("no") : int`, and a `match` whose
alternatives are named `error` and `ok` takes one apart.  Both carry a type, and in both it is the
half the value does not say: an except relates two types and either value pins exactly one of
them.

The five hashmap forms are `hashmap(string, int)`, `m[k]` — the brackets again, read as a lookup for
everything that is not a list — `{ m with [k] = v }`, `map m f` — the keyword again, read as a
hashmap's mapping for a hashmap and a list's for everything else — and `toList m`.  The third is the
shape a struct update is written in, and the brackets are what tell the two apart: a key is an
expression where a field is a name.  The last two are written like `reverse`, as prefix keywords,
because they are the same kind of thing: a map to read and a value of a different type out, with
`map` taking the function to apply as a second operand.

The two tuple forms are `tuple(1, "a")` and `t.0`.  The first is written the way the *type*
`tuple(int, string)` is, with its elements in one comma-separated group; the second is `p.x` with an
index in place of the field name, which is what reading a positional type rather than a named
declaration comes to.

The three struct forms are `new Point { x = 1, y = 2 }`, `p.x`, and `{ p with x = 1 }`.  A field read
is written two ways for one reason: `p.x` is a single identifier token as far as Lean's tokenizer is
concerned, so a dotted identifier that no declaration has taken as a Lean name is split into a
`varRef` and one `structGet` per component, while the postfix `.` is what reads a field of something
that is not a bare name — `f(1).x`, or `(var "my-struct").x`.  The two agree on everything they both
accept, and the postfix form is also what reads a field off a name a declaration *has* taken:
`(var "Foo.bar").baz`, since `Foo.bar.baz` would be the whole IR name.

`unreachable "why" : int` is the branch nothing reaches.  It is annotated the way `none : int` is,
and for a reason of its own: a branch needs the type its siblings have, and there is nothing in this
one for a type to be read off because there is nothing in it at all. -/

syntax :max ident : lgtmExpr

syntax :max num : lgtmExpr

syntax :max str : lgtmExpr

/-- `true` and `false` are the two `bool` literals.  They are keywords rather than identifiers, so
neither is available as a variable name inside a DSL term; `var "true"` is the escape hatch, the same
one `reverse` and `new` leave. -/
syntax :max &"true" : lgtmExpr

syntax :max &"false" : lgtmExpr

syntax :max "(" lgtmExpr ")" : lgtmExpr

syntax :max "~" "(" term ")" : lgtmExpr

/-- `var "x"` is the variable `x`, for IR names that are not Lean identifiers. -/
syntax :max &"var" str : lgtmExpr

syntax :max "[" lgtmExpr,* " : " lgtmTy "]" : lgtmExpr

syntax :max &"reverse" lgtmExpr:max : lgtmExpr

/-- `length xs` is how many elements `xs` has, as an `int`.

A prefix keyword binding as tightly as `reverse`, so `length xs + 1` is the length plus one and
`length (reverse xs)` takes parentheses to reach past one operand.  Unlike `reverse` what comes out
is not a list, which is what makes `length xs == 0` a comparison of two `int`s.

`length` is a keyword, so it is not available as a variable name inside a DSL term; `var "length"`
is the escape hatch, the same one `reverse` and `toList` leave. -/
syntax :max &"length" lgtmExpr:max : lgtmExpr

/-- `min a b` is the smaller of two `int`s and `max a b` the larger.

Prefix keywords taking two operands, the way `sortOn` does, rather than operators like `+` and `-`:
there is no symbol either is written with, and a keyword is what every other binary form the IR has
is written as.  Both operands bind as tightly as `reverse`'s one, so `min x y + 1` is the minimum
plus one and `min (x + 1) y` takes parentheses to reach past the first operand.

Both operands must be `int`s and what comes out is an `int`, which is the type checker's business
rather than the parser's.  Unlike `<` and `<=` neither is polymorphic: a comparison produces a
`bool` whatever it compared, where these hand back one of their operands.

`min` and `max` are keywords, so neither is available as a variable name inside a DSL term;
`var "min"` is the escape hatch, the same one `reverse` and `length` leave. -/
syntax :max &"min" lgtmExpr:max lgtmExpr:max : lgtmExpr

syntax :max &"max" lgtmExpr:max lgtmExpr:max : lgtmExpr

syntax :max lgtmExpr:max noWs "(" lgtmExpr,* ")" : lgtmExpr

/-- `new Point { x = 1, y = 2 }` builds a `Point`.  Every field the declaration has must be given,
in the order it declares them, which is the type checker's business rather than the parser's. -/
syntax :max &"new" ident "{" (ident " = " lgtmExpr),* "}" : lgtmExpr

syntax :max &"new" str "{" (ident " = " lgtmExpr),* "}" : lgtmExpr

/-- `e.field`, for an `e` that is not a bare name.  A bare name takes the dotted-identifier route
instead. -/
syntax :max lgtmExpr:max noWs "." noWs ident : lgtmExpr

/-- `{ p with x = 1, y = 2 }` is `p` with those fields rebound and the rest left alone. -/
syntax :max "{" lgtmExpr " with " (ident " = " lgtmExpr),* "}" : lgtmExpr

/-- `new Color.Rgb(255, 0, 0)` applies the constructor `Rgb` of the inductive type `Color`, and
`new Color.Red()` one that takes nothing — the parentheses are always there, as they are for a call.

The type and the constructor are one dotted identifier because that is how the two are written
everywhere else, and because it is one token as far as Lean's tokenizer is concerned.  Exactly two
components are expected; `new "my-type" "Red"(1)` is the escape hatch for names that are not Lean
identifiers. -/
syntax :max &"new" ident "(" lgtmExpr,* ")" : lgtmExpr

syntax :max &"new" str str "(" lgtmExpr,* ")" : lgtmExpr

/-- `some(e)` is the option holding `e`.  It takes no annotation, because `optionSome` takes none:
the value it holds is what the element type is read off.

Written with parentheses the way a call and a `new` are, and for the same reason the `match`
alternative `| some(x) => ...` is: the one value an option holds is given like the one argument a
constructor takes. -/
syntax :max &"some" "(" lgtmExpr ")" : lgtmExpr

/-- `none : int` is the empty option at `int`, annotated because `optionNone` is: an empty option
holds nothing to read a type off, exactly as an empty list literal does not.

The annotation is a type at `max`, so `none : list int` and `none : option int` need no parentheses
while a function type does: `none : ((int) -> int)`.  Inside a list literal, which ends with an
annotation of its own, the option takes parentheses to say which `:` is which:
`[(none : int) : option int]`.

`none` is a keyword, so neither it nor `some` is available as a variable name inside a DSL term;
`var "none"` is the escape hatch, the same one `true` and `new` leave. -/
syntax :max &"none" " : " lgtmTy:max : lgtmExpr

/-- `ok(1) : string` is the successful `except string int` holding `1`, and
`error("no") : int` the failed one carrying `"no"`.

Both are annotated, and in both the annotation is the *other* half — the one the value says nothing
about.  A success carries a value of the payload type, so what is written after the `:` is the error
type; a failure carries an error, so what is written there is the payload type.  That is
`optionSome` needing no annotation and `optionNone` needing one, read at a type with two halves
instead of one: either value pins exactly the half it carries and leaves the other to be written.

The annotation is a type at `max` and reads the way `none : int` does, so `ok(1) : list string`
needs no parentheses while a function type does — `ok(1) : ((int) -> int)` — and inside a list
literal, which ends with an annotation of its own, it takes parentheses to say which `:` is which.

`ok` and `error` are keywords, so neither is available as a variable name inside a DSL term;
`var "ok"` is the escape hatch, the same one `true`, `none` and `new` leave. -/
syntax :max &"ok" "(" lgtmExpr ")" " : " lgtmTy:max : lgtmExpr

syntax :max &"error" "(" lgtmExpr ")" " : " lgtmTy:max : lgtmExpr

/-- `unreachable "why" : int` is a branch nothing reaches, at `int`, with a note saying why.

Annotated, and read the same way `none : int` is: a type at `max`, so `unreachable "why" : list int`
needs no parentheses while a function type does — `unreachable "why" : ((int) -> int)` — and inside a
list literal, which ends with an annotation of its own, it takes parentheses to say which `:` is
which.

What the annotation is for is the branch rather than the form: both branches of an `if` must have
one type, so this takes whichever one its siblings have, and the type checker asks nothing else of
it.  Nothing else does either — `Eval` has no rule for the form, so a use that is ever reached has
no value, and `Eval.not_unreachable` is what a proof rules one out with.

`unreachable` is a keyword, so it is not available as a variable name inside a DSL term;
`var "unreachable"` is the escape hatch, the same one `none` and `toList` leave. -/
syntax :max &"unreachable" str " : " lgtmTy:max : lgtmExpr

/-- `hashmap(string, int)` is the empty map from `string` to `int`.

Annotated for the reason `[: int]` and `none : int` are: it binds nothing, so there is no key and no
value in it for either type to be read off.  The two are written together and in parentheses, where
a list literal writes its one type after a `:`, because the order is what says which of them is
which.

`hashmap` is a keyword, so it is not available as a variable name inside a DSL term; `var "hashmap"`
is the escape hatch, the same one `true`, `none` and `new` leave. -/
syntax :max &"hashmap" "(" lgtmTy ", " lgtmTy ")" : lgtmExpr

/-- `m[k]` is what `k` is bound to in `m`, and `xs[i]` the element of `xs` at the position `i`.

One form over two readings — `hashmapGet` and `listIndex` — told apart by the type inferred for what
is indexed: a `list` is an index and anything else a lookup.  Both produce an `option`, of the map's
value type and of the list's element type respectively, so neither a key the map does not bind nor a
position the list has no element at is an error, and
`match m[k] with | none => ... | some(x) => ...` is how both cases of either are read.

Where the operand has no type there is nothing to decide by, and the reading is the lookup: that is
what leaves every `m[k]` written before an index existed denoting what it did, and nothing is
reported for it here, since an operand with no type is itself the innermost expression that does not
check and is already reported as such.  What it costs is that an index can only be written where the
operand's type is readable — inside a declaration that is everywhere, while a bare `[lgtm| ...]`
fragment has no context at all, so only an operand carrying its own type is one, and `[lgtm| xs[0]]`
for a free `xs` is a lookup.  `map` below is the other form read this way, and the note on it says
what the two have in common.

Written with no space before the `[`, which is what tells it from a list literal: `m [1 : int]` is
two expressions and no parse, while `m[1]` is a lookup.  It binds as tightly as a field read and
nests the same way — `p.m[k]`, `f(1)[k]`, `m[k1][k2]` — since what either reading produces is an
operand like any other.  Chaining is where the two part company: `m[k1][k2]` is two lookups, where
`xs[i][j]` over a `list list int` is not two indexes — the first hands back an `option`, which is no
list, so the second bracket reads as a lookup and does not check. -/
syntax :max lgtmExpr:max noWs "[" lgtmExpr "]" : lgtmExpr

/-! `map` is one keyword over two forms — a list's mapping and a hashmap's — told apart the way the
brackets above are: by the type inferred for what is mapped over.  A `hashmap` is a hashmap's
mapping and everything else a list's.

A tag saying which would have nowhere to go that reads as the operation does, which is the first of
the bracket form's two reasons over again: `map` is the word every language writing either mapping
writes it as, so tagging means a word neither form wants between the keyword and its operand.  And
the second reason holds here too — a declaration resolves its operands, so the reading inside one is
the reading the types give, and only a bare fragment, which is not type checked at all, can read a
term the declaration around it would have read the other way.

What an `Expression` a term denotes depends on is still a thing to be sparing with, which is why the
deduction is one test of the one type a hashmap's mapping can be written over at all.  A type is
available here only where everything the operand is built from was itself resolved — not through a
splice, not under a `let` whose bound expression is ill typed (see `unknownTy`) — and everything no
type is available for therefore reads as a list's mapping, the commoner of the two and the one a
`map` over a free name in a fragment is overwhelmingly meant as.  The two forms also differ in the
arity of the function, one parameter against two, but that is readable only where the function is
written out as a `fun` and says nothing about `map m f` for a named `f`.

It is one keyword rather than a form apiece because the two mappings are the same operation over the
two things the IR has to map over. -/

/-- `map xs f` is `xs` with `f` applied to each of its elements, and `map m f` is `m` with `f`
applied to each of its bindings — which of the two read off the type of the first operand: a
`hashmap` is a hashmap's mapping, and a list, anything else, or an operand with no type at all a
list's.

Over a list, what comes back is a list of the same length, each element replaced by what `f`
returned for it.  The function takes one parameter, so it is of type `(int) -> string` over a
`list int`, and the result is a `list string` — the element type is the one thing a mapping over a
list does *not* carry through.

Over a hashmap, what comes back is a map from the same keys, each bound to what `f` returned for
that key and the value it was bound to.  The function takes the key as well as the value, so it is
of type `(string, int) -> int` over a `hashmap string int`: two parameters where a list's mapping
takes one.  Both arities, and what either mapping produces, are the type checker's business rather
than the parser's.

The two operands bind as tightly as `reverse`'s one, so `map xs f`, `map p.items g(1)` and
`map p.m g(1)` need no parentheses while a function written out does — a `fun` is the loosest form
there is: `map xs (fun (x : int) => x + 1)` and `map m (fun (k : string) (v : int) => v + 1)`.

`map` is a keyword, so it is not available as a variable name inside a DSL term; `var "map"` is the
escape hatch, the same one `reverse` and `toList` leave. -/
syntax :max &"map" lgtmExpr:max lgtmExpr:max : lgtmExpr

/-- `flatMap xs f` is `f` applied to each element of `xs` and the lists that came back run together:
one list per element, concatenated in the order the elements were in.

The function takes one parameter as a list's mapping's does, but it returns a *list*, so it is of
type `(int) -> list string` over a `list int` — and what comes back is a `list string` rather than a
list of lists.  That it must return a list at all is the type checker's business rather than the
parser's, and it is the whole of what separates this from `map`: the same function under the other
keyword would give a `list (list string)`.

So this is the one list form whose result is not as long as its operand.  A call returning `[: int]`
drops the element it was given and one returning several puts several in its place, which is why
there is a form for it rather than a `map` with something after it.

It is a keyword of its own rather than a third reading of `map`, since what `map` is read by is what
it maps *over* — a list or a hashmap — where this is the other thing to do with the results of
mapping over a list.

The two operands bind as tightly as `map`'s, so `flatMap xs f` and `flatMap p.items g(1)` need
no parentheses while a function written out does: `flatMap xs (fun (x : int) => [x, x : int])`.

`flatMap` is a keyword, so it is not available as a variable name inside a DSL term; `var "flatMap"`
is the escape hatch, the same one `map` and `sortOn` leave. -/
syntax :max &"flatMap" lgtmExpr:max lgtmExpr:max : lgtmExpr

/-- `findIndex xs f` is the position of the first element of `xs` that `f` accepts, as an
`option int`: `some(i)` for the first element `f` answered `true` for, and `none : int` when it
accepts none of them.

The predicate takes one parameter at the element type, as a list's mapping's function does, and
answers with a `bool` — so it is of type `(int) -> bool` over a `list int`, which is the type
checker's business rather than the parser's.  What comes back mentions neither type: an index is a
position rather than anything the list held, which makes this the one list form whose result is
neither a list nor an `int`.  The option is there because a list may hold nothing the predicate
accepts.

The elements after the first match are never handed to the predicate, which is `Eval`'s business
rather than anything here.

The two operands bind as tightly as `sortBy`'s, so `findIndex xs f` and `findIndex p.items g(1)` need
no parentheses while a predicate written out does:
`findIndex xs (fun (x : int) => x == 0)`.

`findIndex` is a keyword, so it is not available as a variable name inside a DSL term;
`var "findIndex"` is the escape hatch, the same one `flatMap` and `sortBy` leave. -/
syntax :max &"findIndex" lgtmExpr:max lgtmExpr:max : lgtmExpr

/-- `sortOn xs f` is `xs` with its elements in the order `f`'s results put them in: `f` is applied to
each element to get the key that element is ordered by.

The projection takes one parameter, as a list's mapping's function does, so it is of type
`(int) -> string` over a `list int` — and unlike a mapping, what comes back is a `list int` still.
The key's type is the one thing the result does not mention: it must be a type with an ordering,
which is the type checker's business rather than the parser's, and the elements it ordered are
handed back unchanged.

Elements sharing a key keep the order they were in, which is what `Eval` says of the form rather
than anything here.

The two operands bind as tightly as `map`'s, so `sortOn xs f` and `sortOn p.items g(1)` need no
parentheses while a projection written out does: `sortOn xs (fun (x : int) => 0 - x)`.

`sortOn` is a keyword, so it is not available as a variable name inside a DSL term; `var "sortOn"`
is the escape hatch, the same one `reverse` and `map` leave. -/
syntax :max &"sortOn" lgtmExpr:max lgtmExpr:max : lgtmExpr

/-- `sortBy xs f` is `xs` with its elements in the order `f`'s answers put them in: `f` is applied to
two elements and says whether the first comes first.

The comparison takes two parameters at the element type and returns a `bool`, so it is of type
`(int, int) -> bool` over a `list int` — and what comes back is a `list int`, as `sortOn`'s does.
Being a `bool` is all that is asked of its result, which is the type checker's business rather than
the parser's, and it is the whole of what separates the two sorts: a key must be of a type with an
ordering, where a comparison *is* the ordering and so needs none.  That is what lets this sort a list
of anything at all, including the types `sortOn` could order by nothing.

Elements the comparison does not separate keep the order they were in, which is what `Eval` says of
the form rather than anything here.

The two operands bind as tightly as `sortOn`'s, so `sortBy xs f` and `sortBy p.items g(1)` need no
parentheses while a comparison written out does:
`sortBy xs (fun (a : int) (b : int) => b <= a)`.

`sortBy` is a keyword, so it is not available as a variable name inside a DSL term; `var "sortBy"`
is the escape hatch, the same one `sortOn` and `map` leave. -/
syntax :max &"sortBy" lgtmExpr:max lgtmExpr:max : lgtmExpr

/-- `toList m` is the bindings of `m` as a list, one `tuple(k, v)` per binding, in the order the map
carries them.

A prefix keyword binding as tightly as `reverse`, so `toList m` is a lookup's operand away from
`toList p.m` and `toList f(1)` and takes parentheses to reach further: `toList (m[k])` is not a map
and does not type check, which is the type checker's business rather than the parser's.

`toList` is a keyword, so it is not available as a variable name inside a DSL term; `var "toList"`
is the escape hatch, the same one `reverse` and `hashmap` leave. -/
syntax :max &"toList" lgtmExpr:max : lgtmExpr

/-- One binding of a hashmap update: the key, in brackets, and what to bind it to. -/
public syntax lgtmKeyBinding := "[" lgtmExpr "]" " = " lgtmExpr

/-- `{ m with [k] = v }` is `m` with `k` bound to `v`, and any previous binding for `k` dropped.

The shape a struct update is written in, because it is the same thing of a map: `{ p with x = 1 }`
rebinds a field the declaration named, and this rebinds a key the map need never have seen.  Which
of the two a `{ ... with ... }` is comes from the brackets — a key is an expression and a field is a
name, so there is no term both could be read as, and no update may mix them.

Several bindings are one `hashmapPut` apiece, applied left to right, so
`{ m with [a] = 1, [b] = 2 }` is `{ { m with [a] = 1 } with [b] = 2 }`.  At least one is required:
`{ m with }` is the struct update it has always been. -/
syntax :max "{" lgtmExpr " with " lgtmKeyBinding,+ "}" : lgtmExpr

/-- `tuple(1, "a")` is an `int` beside a `string`.

Written the way the type `tuple(int, string)` is and for the same reason: a tuple takes any number
of elements, so where the comma-separated group ends is what says how many there are.  `tuple()` is
the empty tuple.

It carries no annotation, unlike `[: int]` and `none : int` and `hashmap(string, int)`: the elements
are what the types are read off, and the empty tuple needs none either — `tuple()` has the one type
it could have, where an empty list has every list type.

`tuple` is a keyword, so it is not available as a variable name inside a DSL term; `var "tuple"` is
the escape hatch, the same one `true`, `none`, `hashmap` and `new` leave. -/
syntax :max &"tuple" "(" lgtmExpr,* ")" : lgtmExpr

/-- `t.0` is the first element of the tuple `t`, `t.1` the second.

The positional counterpart of `p.x`, and written to look like one: the index takes the place of the
field name, because a tuple type carries its types where a struct names a declaration that carries
its fields.  It binds as tightly as a field read and nests the same way — `p.t.0`, `f(1).0`,
`m[k].0` — since what one produces is an operand like any other.

What it cannot nest *into* is itself, because of Lean's tokenizer rather than anything here: `t.0.1`
reads `0.1` as a decimal and `t.0.x` reads `0.x` as an attempt at one, so taking something out of an
element takes parentheses — `(t.0).1` and `(t.0).x`.  That is the same kind of cost `m[k]` pays for
being written with no space before the `[`.

The index is a literal rather than an expression, which is what makes the form typeable: a tuple is
heterogeneous, so the type that comes out is the one the tuple type gives at that position, and
there is no type to give for a position that is not known until something runs.  An index past the
end is therefore ill typed rather than a failure at run time, which is the type checker's business
rather than the parser's. -/
syntax :max lgtmExpr:max noWs "." noWs num : lgtmExpr

/-- One alternative of a `match`: the constructor's name, the names to bind the values it carries to,
and the expression to evaluate when the value was built by it.  A constructor that carries nothing
takes no parentheses.

`none`, `some`, `error` and `ok` are read as keywords here rather than as identifiers, so that an
editor colours them the way it colours the expression forms of those names — a token is what
semantic highlighting is given, and an identifier the DSL binds no Lean variable for is given
nothing.  The heads are tried in that order and an identifier last, so every other constructor still
parses as one; `elabLgtmExpr` stands the identifier a keyword head names back in its place, so
nothing after the parser tells the two apart. -/
public syntax lgtmAlt :=
  " | " (&"none" <|> &"some" <|> &"error" <|> &"ok" <|> ident) ("(" ident,* ")")? " => " lgtmExpr

/-- `match c with | Red => 0 | Rgb(r, g, b) => r` takes a value of an inductive type apart.

The alternatives have to be the type's constructors in the order it declares them, which is the type
checker's business rather than the parser's.  An alternative's expression extends as far right as it
can, so a `match` nested inside one needs parentheses — the same way a `let` does.

`match o with | none => 0 | some(x) => x` and
`match r with | error(e) => 0 | ok(x) => x` are the two special cases: alternatives named `none` and
`some` make an `optionMatch` and ones named `error` and `ok` an `exceptMatch`, since each of those
types is taken apart by a form of its own.  Either pair has to be both of its alternatives and in
that order, which the parser does not ask of the alternatives of an `indMatch` but which these ask
here — each form holds the two cases its type has rather than a list to check against a declaration,
so there is nothing for a third alternative or a missing one to mean.  The cost is that an inductive
type declaring a constructor called `none`, `some`, `error` or `ok` is one this syntax cannot match
on; `~(Expression.indMatch ...)` is the way to write that one. -/
syntax :10 "match " lgtmExpr " with" lgtmAlt* : lgtmExpr

/-! A match on a list is a `listMatch`, which is a form of its own the way `optionMatch` is, and its
alternatives are written with the tokens a *list* is written with rather than with constructor names:
`[]` for the empty list and `hd :: tl` for one with a head.  Neither is a name, so they are a
category of their own rather than `lgtmAlt`s — an alternative there is a constructor's name and the
names it binds — and that is also what keeps the two readings of a `match` apart with nothing to
decide.  Where `optionMatchAlts` chooses between an option and a declared inductive type, a parse of
these alternatives is a match on a list already; the cost `optionMatch` pays, of an inductive type
that declares a constructor called `none`, is one this form does not pay at all. -/
declare_syntax_cat lgtmListAlt

/-- The empty-list alternative of a match on a list: `| [] => e`.  It binds no names, since an empty
list holds nothing — the way `none`'s alternative binds none. -/
syntax " | " "[" "]" " => " lgtmExpr : lgtmListAlt

/-- The non-empty alternative of a match on a list: `| hd :: tl => e`, with the head and the tail of
the list bound to those two names in `e`.

Two names rather than the one `some(x)` binds, which is the whole of what makes this more than a
match on an option: a list's tail is a list, so the names stand at the element type and at the
scrutinee's own list type.  They are IR names like every other binder here, so `tl` refers to the
tail and never to a Lean variable of that name. -/
syntax " | " ident " :: " ident " => " lgtmExpr : lgtmListAlt

/-- `match xs with | [] => 0 | hd :: tl => hd` takes a list apart.

Both alternatives are required and in that order, as a match on an option's are and for the same
reason: the form holds the two cases a list has rather than a list of alternatives to check against a
declaration, so there is nothing for a third alternative or a missing one to mean.

An alternative's expression extends as far right as it can, exactly as an `indMatch`'s does, so a
`match` nested inside one needs parentheses — the same way a `let` does. -/
syntax :10 "match " lgtmExpr " with" lgtmListAlt+ : lgtmExpr

/-- `if b then ( 1 ) else ( 2 )` chooses between its two branches.

The branches are parenthesized, and those parentheses are part of the form rather than optional, so
it ends where the last `)` does and needs nothing further to be an operand: `if b then ( 1 ) else
( 2 ) + 1` adds to the conditional rather than to its second branch, which is the opposite of how a
`let` or a `match` alternative reads.  The condition takes no parentheses because `then` is what ends
it.

Both branches must have the same type and the condition must be a `bool`, which is the type checker's
business rather than the parser's. -/
syntax :max "if " lgtmExpr " then " "(" lgtmExpr ")" " else " "(" lgtmExpr ")" : lgtmExpr

syntax :65 lgtmExpr:65 " + " lgtmExpr:66 : lgtmExpr

syntax :65 lgtmExpr:65 " - " lgtmExpr:66 : lgtmExpr

syntax :55 lgtmExpr:56 " :: " lgtmExpr:55 : lgtmExpr

/-- `a == b` compares two values structurally, however deep they are.

It is the loosest of the operators but the two boolean ones, so `x + 1 == y` and `x :: xs == ys`
need no parentheses, and it is non-associative: `a == b == c` is a parse error rather than one of
the two comparisons it could have meant.  A comparison *of* comparisons is written with the parentheses that
say which, since what one produces is an ordinary `bool`.

The operands must have the same type, and it must be a type a comparison can reach the bottom of —
which is the type checker's business rather than the parser's. -/
syntax :50 lgtmExpr:51 " == " lgtmExpr:51 : lgtmExpr

/-- `a < b` is `true` when `a` comes before `b` in its type's ordering, and `a <= b` when it comes
before it or is it.

They sit at `==`'s level and do not associate either, so `x + 1 < y` and `length xs <= 0` need no
parentheses while `a < b <= c` and `a < b == c` are parse errors rather than one of the readings
each could have had.  What they produce is an ordinary `bool`, so a comparison of two of them is written
with the parentheses that say which: `(a < b) == c`.

The operands must have the same type and it must be one with an ordering — `int` or `string`, or an
`option`, `list` or `tuple` of those, compared lexicographically — which is the type checker's
business rather than the parser's.

These two are the whole of the IR's ordering: `a > b` is `b < a` written the other way round, so
there is no form for it here. -/
syntax :50 lgtmExpr:51 " < " lgtmExpr:51 : lgtmExpr

syntax :50 lgtmExpr:51 " <= " lgtmExpr:51 : lgtmExpr

/-- `a && b` is `true` when both operands are, and `a || b` when either is.

They are the two loosest operators there are, `||` looser than `&&` and both looser than `==`, so
`x == y && b` and `length xs == 0 || b` need no parentheses and `a || b && c` is `a || (b && c)` —
the precedences every other language writing them this way gives them.  Both are left-associative,
unlike `==`: `a && b && c` is `(a && b) && c`, which is the same answer either grouping would give.

Both operands must be `bool`s, which is the type checker's business rather than the parser's.  The
second is evaluated only when the first did not settle the answer, which is neither's — it is what
`Eval` says of `boolAnd` and `boolOr`. -/
syntax :40 lgtmExpr:40 " && " lgtmExpr:41 : lgtmExpr

syntax :35 lgtmExpr:35 " || " lgtmExpr:36 : lgtmExpr

syntax :10 "fun" ("(" ident " : " lgtmTy ")")* " => " lgtmExpr:10 : lgtmExpr

/-- `let x := e; body`, spelled the way Lean's own `let` is.  The bound expression carries no
annotation, because `let_` does not: the type checker infers it.  The body extends as far right as
it can, so `let`s chain without parentheses. -/
syntax :10 "let " ident " := " lgtmExpr "; " lgtmExpr:10 : lgtmExpr

/-- `[lgtm| e]` is the `Expression` that `e` denotes. -/
syntax :max "[lgtm| " lgtmExpr "]" : term

/-- The alternatives of a `match` read as an option's, when they are: the body of its `none` case,
the name its `some` case binds, and the body under it.

`none` when no alternative names either `none` or `some`, which is every other `match` and is an
`indMatch`; an error when one does and the rest of the shape is not an option's, because there is no
second reading to fall back on — a `match` mentioning `none` is one the writer meant for an option.

Only the shape is decided here.  The three pieces come back as syntax for `elabLgtmExpr` to read,
which is what keeps the recursion in one place. -/
meta def optionMatchAlts
    (alts : Array (Ident × Array Ident × TSyntax `lgtmExpr)) :
    LgtmElabM (Option (TSyntax `lgtmExpr × Ident × TSyntax `lgtmExpr)) := do
  let isOptionCtor (c : Ident) : Bool := c.getId == `none || c.getId == `some
  let some (named, _, _) := alts.find? (fun (c, _, _) => isOptionCtor c) | return none
  let #[(nc, nxs, nbody), (sc, sxs, sbody)] := alts
    |
    throwErrorAt named
        "a match on an option has two alternatives: `| none => ... | some(x) => ...`"
  unless nc.getId == `none && sc.getId == `some do
    throwErrorAt named "a match on an option takes `none` first and `some` second"
  unless nxs.isEmpty do
    throwErrorAt nc "`none` holds nothing, so its alternative binds no names"
  let #[x] := sxs
    |
    throwErrorAt sc
        "`some` holds one value, so its alternative binds one name: `| some(x) => ...`"
  return some (nbody, x, sbody)

/-- The alternatives of a `match` read as an except's, when they are: the name its `error` case
binds and the body under it, then the same for its `ok` case.

`optionMatchAlts` with a name in both cases rather than in one, and read the same way: `none` when
no alternative names either `error` or `ok`, and an error when one does and the rest of the shape is
not an except's, because there is no second reading to fall back on. -/
meta def exceptMatchAlts
    (alts : Array (Ident × Array Ident × TSyntax `lgtmExpr)) :
    LgtmElabM (Option (Ident × TSyntax `lgtmExpr × Ident × TSyntax `lgtmExpr)) := do
  let isExceptCtor (c : Ident) : Bool := c.getId == `error || c.getId == `ok
  let some (named, _, _) := alts.find? (fun (c, _, _) => isExceptCtor c) | return none
  let #[(ec, exs, ebody), (oc, oxs, obody)] := alts
    |
    throwErrorAt named
        "a match on an except has two alternatives: `| error(e) => ... | ok(x) => ...`"
  unless ec.getId == `error && oc.getId == `ok do
    throwErrorAt named "a match on an except takes `error` first and `ok` second"
  let #[x] := exs
    |
    throwErrorAt ec
        "`error` holds one value, so its alternative binds one name: `| error(e) => ...`"
  let #[y] := oxs
    |
    throwErrorAt oc "`ok` holds one value, so its alternative binds one name: `| ok(x) => ...`"
  return some (x, ebody, y, obody)

/-- The alternatives of a match on a list read as the two cases it has: the body of its `[]` case,
the names its `::` case binds, and the body under them.

There is no reading to fall back on and so no `Option` here, unlike `optionMatchAlts`: alternatives
written with `[]` and `::` are a match on a list and nothing else, so what is left is the shape —
both cases, in that order — and anything else is an error.  Reported at the first alternative, which
is where the shape of the whole is decided.

Only the shape is decided here.  The four pieces come back as syntax for `elabLgtmExpr` to read,
which is what keeps the recursion in one place. -/
meta def listMatchAlts (ref : Syntax) (alts : Array (TSyntax `lgtmListAlt)) :
    LgtmElabM (TSyntax `lgtmExpr × Ident × Ident × TSyntax `lgtmExpr) := do
  let shape := "a match on a list has two alternatives: `| [] => ... | hd :: tl => ...`"
  let at? := (alts[0]?.map TSyntax.raw).getD ref
  let #[nilAlt, consAlt] := alts | throwErrorAt at? shape
  match nilAlt, consAlt with
  | `(lgtmListAlt| | [] => $nbody), `(lgtmListAlt| | $hd:ident :: $tl:ident => $cbody) =>
      return (nbody, hd, tl, cbody)
  | `(lgtmListAlt| | $_:ident :: $_:ident => $_), `(lgtmListAlt| | [] => $_) =>
      throwErrorAt at? "a match on a list takes `[]` first and `::` second"
  | _, _ => throwErrorAt at? shape

/-! ## Resolving names

A name the DSL mentions is resolved against the parameters and `let`s it is written under and the
declarations in scope, and a name neither of them has is reported where it is written.  That is the
half of the checking a type checker is the wrong thing to do: `Expression.inferE` reports a name it
cannot find too, but one form out and about the body it was reached through, where this reports it
on the token itself and can say which declared name it looks like.

What can be resolved this way is what a name alone decides: a variable, a struct or inductive type,
a constructor of a named type, a field of a `new`, and how many arguments a named declaration takes.
What cannot is anything needing a type first — the alternatives of a `match`, the field of a
`p.x` — since the type of what is being taken apart is exactly what inference is for. -/

/-- Report at `ref` unless `name` is a variable bound by the term or a declaration in scope. -/
private meta def checkVarName (ref : Syntax) (bound : List String) (name : String) :
    LgtmElabM Unit := do
  if bound.contains name then
    addIrNameInfo ref name
    return
  let ctx ← read
  if (ctx.allGlobals.lookup name).isSome then
    addIrNameInfo ref name
    return
  reportAt ref
    (withSuggestion name (bound ++ ctx.allGlobals.map Prod.fst)
      s!"no variable named '{name}' is in scope")

/-- Report at `ref` unless the dotted `name` reads as a field of something: its first component
`root` has to be a variable, since the whole of it is not a declaration.

Reported over the whole name rather than over `root`, and against the declared names as well as the
variables, because the mistake is almost always in the whole: a dotted name is how one declaration
calls another, so one that reaches neither is a call of something misspelled or renamed far more
often than a field read of a variable that does not exist. -/
private meta def checkDottedName (ref : Syntax) (bound : List String) (name root : String) :
    LgtmElabM Unit := do
  if bound.contains root then return
  let ctx ← read
  if (ctx.allGlobals.lookup root).isSome then return
  reportAt ref
    (withSuggestion name (ctx.scope.names ++ ctx.extra.names ++ bound)
      s!"nothing named '{name}' is declared, and '{root}' is not a variable in scope")

/-- Report at `ref` unless `ctor` is a constructor of the inductive type `tyName` and carries
`arity` values.

Silent when `tyName` names nothing: the mistake is then the type name, which `checkIndName` has
already reported, and saying anything further about the constructor of a type that does not exist
would be describing the same mistake twice. -/
private meta def checkCtorArity (ref : Syntax) (tyName ctor : String) (arity : Nat) :
    LgtmElabM Unit := do
  let some d := (← read).allInductives.lookup tyName | return
  match d.constructors.lookup ctor with
  | none =>
      reportAt ref
        (withSuggestion ctor (d.constructors.map Prod.fst)
          s!"inductive '{tyName}' has no constructor named '{ctor}'")
  | some ts =>
      unless ts.length == arity do
        reportAt ref
          s!"constructor '{ctor}' of inductive '{tyName}' carries {ts.length} value(s), but \
            {arity} are given here"

/-- Report at `ref` unless `field` is one the struct `name` declares. -/
private meta def checkFieldName (ref : Syntax) (name field : String) : LgtmElabM Unit := do
  let some d := (← read).allStructs.lookup name | return
  if (d.fields.lookup field).isSome then return
  reportAt ref
    (withSuggestion field (d.fields.map Prod.fst) s!"struct '{name}' has no field named '{field}'")

/-- Report at `ref` when `f` is a declaration in scope and is given the wrong number of arguments.

Nothing is said about a call of anything else: what is applied has a type the type checker finds
rather than a declaration to count the parameters of. -/
private meta def checkCallArity (ref : Syntax) (f : Expression) (arity : Nat) : LgtmElabM Unit := do
  let .varRef name := f | return
  let some d := (← read).allGlobals.lookup name | return
  unless d.parameters.length == arity do
    reportAt ref
      s!"'{name}' takes {d.parameters.length} argument(s), but {arity} are given here"

/-- Record on the name that binds it the type a binder stands at.

The expressions of a declaration are recorded by `addNodeTyInfo`, which has nothing to say about a
binder: the name in `let x := ...` is a token of the form that binds it rather than an expression of
its own, so the innermost expression written over it is the whole `let`, whose type is its body's.

Silent for a fragment, which is not checked, and for a binder standing at `unknownTy`, which is what
is recorded when what it binds has no type — there is nothing to show and the expression that had no
type is itself reported. -/
private meta def addBinderTyInfo (x : Ident) (t : Ty) : LgtmElabM Unit := do
  if (← read).report && t != unknownTy then
    addTyInfo x t

mutual
/-- Build the `Expression` that `stx` denotes, under the context `ctx`.

The context carries the types as well as the names, because the two things this pass does with it
need both: a name nothing binds is reported from the names, and the node recorded for every
expression is recorded with the context it would be checked in, which is what makes the type
checker's report land on the part of the term it is about.

What `ctx` holds is what `FuncDecl.check` would hold at the same point — the parameters, the
globals' types, and a binding per `fun`, `let` and `match` alternative passed through on the way in.
`unknownTy` is where the two can come apart, and says why they cannot come apart in a way anything
is reported from. -/
meta partial def elabLgtmExpr (ctx : Context) (stx : TSyntax `lgtmExpr) :
    LgtmElabM Expression := do
  let e ← elabLgtmExprCore ctx stx
  if (← read).report then
    modify fun st => { st with nodes := st.nodes.push (stx, e, ctx) }
  return e

/-- The type `stx`'s expression has, or `unknownTy` when it has none.  Used where a binder's type is
read off what it is bound to, by the brackets of `m[k]` to tell an index from a lookup, and by `map`
to tell a list's mapping from a hashmap's. -/
meta partial def inferredTy (ctx : Context) (e : Expression) : LgtmElabM Ty := do
  match e.inferE (← read).allTypeDecls ctx with
  | .ok t => return t
  | .error _ => return unknownTy

/-- The cases of `elabLgtmExpr`, which is this with the recording around it. -/
meta partial def elabLgtmExprCore (ctx : Context) (stx : TSyntax `lgtmExpr) :
    LgtmElabM Expression := do
  let names := ctx.map Prod.fst
  let elabList (es : Array (TSyntax `lgtmExpr)) : LgtmElabM (List Expression) :=
    es.toList.mapM (elabLgtmExpr ctx)
  let elabFields (owner : Option String) (fs : Array Ident) (es : Array (TSyntax `lgtmExpr)) :
      LgtmElabM (List (FieldName × Expression)) :=
    (fs.zip es).toList.mapM fun (f, e) => do
      let field := f.getId.toString
      if let some name := owner then
        checkFieldName f name field
      return (field, ← elabLgtmExpr ctx e)
  match stx with
  | `(lgtmExpr| $x:ident) => do
      -- `p.x.y` arrives here as one identifier, because that is how it tokenizes, and the two
      -- things it can mean are told apart by what is declared.  A name an `lgtm` declaration
      -- already took is a `varRef` of the whole of it, so `CommentThreads.empty()` calls that
      -- declaration.  Any other name is a variable and one field read per component after the
      -- first.
      let name := x.getId.toString
      if ((← read).scope.find? name).isSome then
        addIrNameInfo x name
        return .varRef name
      match name.splitOn "." with
      | [] => throwErrorAt x "an identifier with no name"
      | root :: fields => do
          if fields.isEmpty then
            checkVarName x names root
          else
            checkDottedName x names name root
          return fields.foldl (init := .varRef root) fun acc f => .structGet acc f
  | `(lgtmExpr| var $s:str) => do
      checkVarName s names s.getString
      return .varRef s.getString
  | `(lgtmExpr| true) => return .boolLit true
  | `(lgtmExpr| false) => return .boolLit false
  | `(lgtmExpr| $n:num) => return .intLit n.getNat
  | `(lgtmExpr| $s:str) => return .stringLit s.getString
  | `(lgtmExpr| ($e)) => elabLgtmExpr ctx e
  | `(lgtmExpr| ~($e)) => return .varRef (← elabSplice e ``Expression)
  | `(lgtmExpr| $a + $b) => return .plus (← elabLgtmExpr ctx a) (← elabLgtmExpr ctx b)
  | `(lgtmExpr| $a - $b) => return .minus (← elabLgtmExpr ctx a) (← elabLgtmExpr ctx b)
  | `(lgtmExpr| $a :: $b) => return .lcons (← elabLgtmExpr ctx a) (← elabLgtmExpr ctx b)
  | `(lgtmExpr| $a == $b) => return .equals (← elabLgtmExpr ctx a) (← elabLgtmExpr ctx b)
  | `(lgtmExpr| $a < $b) => return .lt (← elabLgtmExpr ctx a) (← elabLgtmExpr ctx b)
  | `(lgtmExpr| $a <= $b) => return .le (← elabLgtmExpr ctx a) (← elabLgtmExpr ctx b)
  | `(lgtmExpr| $a && $b) => return .boolAnd (← elabLgtmExpr ctx a) (← elabLgtmExpr ctx b)
  | `(lgtmExpr| $a || $b) => return .boolOr (← elabLgtmExpr ctx a) (← elabLgtmExpr ctx b)
  | `(lgtmExpr| min $a $b) => return .min (← elabLgtmExpr ctx a) (← elabLgtmExpr ctx b)
  | `(lgtmExpr| max $a $b) => return .max (← elabLgtmExpr ctx a) (← elabLgtmExpr ctx b)
  | `(lgtmExpr| reverse $e) => return .listReverse (← elabLgtmExpr ctx e)
  | `(lgtmExpr| length $e) => return .listLength (← elabLgtmExpr ctx e)
  | `(lgtmExpr| [$es,* : $t]) => do
      let t ← elabLgtmTy t
      let es ← elabList es.getElems
      return es.foldr (init := .lnil t) .lcons
  | `(lgtmExpr| $f($args,*)) => do
      let f' ← elabLgtmExpr ctx f
      let as ← elabList args.getElems
      checkCallArity stx f' as.length
      return .app f' as
  | `(lgtmExpr| fun $[($xs:ident : $ts:lgtmTy)]* => $b) => do
      let ps ← (xs.zip ts).toList.mapM fun (x, t) => do
        let t ← elabLgtmTy t
        addBinderTyInfo x t
        return (x.getId.toString, t)
      return .lam ps (← elabLgtmExpr (ps ++ ctx) b)
  | `(lgtmExpr| let $x:ident := $e; $b) => do
      let bnd ← elabLgtmExpr ctx e
      let t ← inferredTy ctx bnd
      addBinderTyInfo x t
      let name := x.getId.toString
      return .let_ name bnd (← elabLgtmExpr ((name, t) :: ctx) b)
  | `(lgtmExpr| if $c then ( $thn ) else ( $els )) =>
      return .ite (← elabLgtmExpr ctx c) (← elabLgtmExpr ctx thn) (← elabLgtmExpr ctx els)
  | `(lgtmExpr| new $n:ident { $[$fs:ident = $es:lgtmExpr],* }) => do
      let name := n.getId.toString
      checkStructName n name
      return .structNew name (← elabFields (some name) fs es)
  | `(lgtmExpr| new $n:str { $[$fs:ident = $es:lgtmExpr],* }) => do
      checkStructName n n.getString
      return .structNew n.getString (← elabFields (some n.getString) fs es)
  | `(lgtmExpr| $e.$f:ident) => do
      let e ← elabLgtmExpr ctx e
      return (f.getId.toString.splitOn ".").foldl (init := e) fun acc g => .structGet acc g
  | `(lgtmExpr| { $e with $[$fs:ident = $es:lgtmExpr],* }) => do
      -- The type of what is being updated is what says which fields it has, so the names are the
      -- type checker's business here where a `new` names the struct and settles them.
      return .structUpdate (← elabLgtmExpr ctx e) (← elabFields none fs es)
  | `(lgtmExpr| new $n:ident($args,*)) => do
      match n.getId.toString.splitOn "." with
      | [ty, c] => do
          checkIndName n ty
          let as ← elabList args.getElems
          checkCtorArity n ty c as.length
          return .indNew ty c as
      | _ =>
          throwErrorAt n
            "a constructor is written `new Type.Ctor(...)`, with the type and the constructor it \
             belongs to"
  | `(lgtmExpr| new $ty:str $c:str($args,*)) => do
      checkIndName ty ty.getString
      let as ← elabList args.getElems
      checkCtorArity c ty.getString c.getString as.length
      return .indNew ty.getString c.getString as
  | `(lgtmExpr| hashmap($k, $v)) => return .hashmapEmpty (← elabLgtmTy k) (← elabLgtmTy v)
  | `(lgtmExpr| $m[$k]) => do
      -- One form over two readings, told apart by the type inferred for what is indexed: a list is
      -- an index and anything else a lookup.  An operand with no type is a lookup too, which is
      -- what leaves every `m[k]` written before an index existed reading as it did.
      let m ← elabLgtmExpr ctx m
      let k ← elabLgtmExpr ctx k
      match ← inferredTy ctx m with
      | .list _ => return .listIndex m k
      | _ => return .hashmapGet m k
  | `(lgtmExpr| map $l $f) => do
      -- One form over two readings, told apart by the type inferred for what is mapped over: a
      -- hashmap is a hashmap's mapping and anything else — an operand with no type included — a
      -- list's, which is the commoner of the two.
      let l ← elabLgtmExpr ctx l
      let f ← elabLgtmExpr ctx f
      match ← inferredTy ctx l with
      | .hashmap _ _ => return .hashmapMap l f
      | _ => return .listMap l f
  | `(lgtmExpr| flatMap $l $f) =>
      return .listFlatMap (← elabLgtmExpr ctx l) (← elabLgtmExpr ctx f)
  | `(lgtmExpr| findIndex $l $f) =>
      return .listFindIndex (← elabLgtmExpr ctx l) (← elabLgtmExpr ctx f)
  | `(lgtmExpr| sortOn $l $f) =>
      return .listSortOn (← elabLgtmExpr ctx l) (← elabLgtmExpr ctx f)
  | `(lgtmExpr| sortBy $l $f) =>
      return .listSortBy (← elabLgtmExpr ctx l) (← elabLgtmExpr ctx f)
  | `(lgtmExpr| toList $m) => return .hashmapToList (← elabLgtmExpr ctx m)
  | `(lgtmExpr| { $m with $bs:lgtmKeyBinding,* }) => do
      let mut acc ← elabLgtmExpr ctx m
      for b in bs.getElems do
        match b with
        | `(lgtmKeyBinding| [$k] = $v) =>
            acc := .hashmapPut acc (← elabLgtmExpr ctx k) (← elabLgtmExpr ctx v)
        | _ => throwErrorAt b "not a binding of a hashmap update"
      return acc
  | `(lgtmExpr| tuple($es,*)) => return .tupleNew (← elabList es.getElems)
  | `(lgtmExpr| $e.$i:num) => return .tupleGet (← elabLgtmExpr ctx e) i.getNat
  | `(lgtmExpr| some($e)) => return .optionSome (← elabLgtmExpr ctx e)
  | `(lgtmExpr| none : $t) => return .optionNone (← elabLgtmTy t)
  | `(lgtmExpr| ok($e) : $t) => return .exceptOk (← elabLgtmTy t) (← elabLgtmExpr ctx e)
  | `(lgtmExpr| error($e) : $t) => return .exceptError (← elabLgtmTy t) (← elabLgtmExpr ctx e)
  | `(lgtmExpr| unreachable $why:str : $t) => return .unreachable (← elabLgtmTy t) why.getString
  | `(lgtmExpr| match $e with $alts:lgtmListAlt*) => do
      let scrut ← elabLgtmExpr ctx e
      let scrutTy ← inferredTy ctx scrut
      let (nbody, hd, tl, cbody) ← listMatchAlts stx alts
      -- `hd :: tl` binds at what the scrutinee's list holds and at that list type itself, which is
      -- how `Expression.inferE` reads the two.  A scrutinee with no type leaves both unknown rather
      -- than the tail at a list of nothing: a binder at `unknownTy` is one nothing is shown for.
      let (hdTy, tlTy) := match scrutTy with
        | .list t => (t, Ty.list t)
        | _ => (unknownTy, unknownTy)
      addBinderTyInfo hd hdTy
      addBinderTyInfo tl tlTy
      let hdName := hd.getId.toString
      let tlName := tl.getId.toString
      return .listMatch scrut (← elabLgtmExpr ctx nbody) hdName tlName
        (← elabLgtmExpr ((hdName, hdTy) :: (tlName, tlTy) :: ctx) cbody)
  | `(lgtmExpr| match $e with $alts:lgtmAlt*) => do
      -- A `none` or `some` head is a keyword token where the others have an identifier.  Standing
      -- the identifier it names in its place, at the token's position, is what lets the readings
      -- below take every head the same way and keeps an error reported on the token itself.
      let withIdentHead (alt : TSyntax `lgtmAlt) : TSyntax `lgtmAlt :=
        let head := alt.raw[1]
        if head.isIdent then alt
        else ⟨alt.raw.setArg 1 (mkIdentFrom head[0] (.mkSimple head[0].getAtomVal))⟩
      let parsed ← alts.mapM fun alt =>
        match withIdentHead alt with
        | `(lgtmAlt| | $c:ident $[($xs:ident,*)]? => $b:lgtmExpr) =>
            return (c, (xs.map (·.getElems)).getD #[], b)
        | _ => throwErrorAt alt "not an alternative of a match"
      let scrut ← elabLgtmExpr ctx e
      let scrutTy ← inferredTy ctx scrut
      -- An alternative named `none` or `some` is a match on an option rather than on a declared
      -- inductive type, and is the one form taking it apart.
      if let some (nbody, x, sbody) ← optionMatchAlts parsed then
        -- `some(x)` binds at what the option holds, which is read off the scrutinee the way
        -- `Expression.inferE` reads it.
        let elemTy := match scrutTy with
          | .option t => t
          | _ => unknownTy
        addBinderTyInfo x elemTy
        let name := x.getId.toString
        return .optionMatch scrut (← elabLgtmExpr ctx nbody) name
          (← elabLgtmExpr ((name, elemTy) :: ctx) sbody)
      -- And one named `error` or `ok` a match on an except, the other type taken apart by a form of
      -- its own.
      if let some (x, ebody, y, obody) ← exceptMatchAlts parsed then
        -- Each case binds at the half of the scrutinee's type its case is for, which is how
        -- `Expression.inferE` reads the two.
        let (errTy, okTy) := match scrutTy with
          | .except e t => (e, t)
          | _ => (unknownTy, unknownTy)
        addBinderTyInfo x errTy
        addBinderTyInfo y okTy
        let errName := x.getId.toString
        let okName := y.getId.toString
        return .exceptMatch scrut errName (← elabLgtmExpr ((errName, errTy) :: ctx) ebody) okName
          (← elabLgtmExpr ((okName, okTy) :: ctx) obody)
      -- An alternative binds at the types its constructor carries, which the declaration of the
      -- scrutinee's type is what gives.
      let inds := (← read).allInductives
      let ctors : List (CtorName × List Ty) := match scrutTy with
        | .ind name => ((inds.lookup name).map InductiveDecl.constructors).getD []
        | _ => []
      let as ← parsed.toList.mapM fun (c, xs, b) => do
        let ns := xs.toList.map fun x => x.getId.toString
        let ts := (ctors.lookup c.getId.toString).getD []
        let binders := ns.zip (ts ++ List.replicate ns.length unknownTy)
        for (x, (_, t)) in xs.toList.zip binders do
          addBinderTyInfo x t
        return (c.getId.toString, ns, ← elabLgtmExpr (binders ++ ctx) b)
      return .indMatch scrut as
  | _ => throwErrorAt stx "not an expression of the `lgtm` language"
end

/-- The first expression of `nodes` that does not type check, with the message saying why.

The entries are in the order they were finished, so the first one failing is the innermost: what
`Expression.inferE` reports of a nest of forms is what it could not do innermost, and this is the
part of the source that was.

`none` when every node checks, which a declaration that does not check can still manage — a body
whose type is not the one declared for it is a disagreement between the body and its signature
rather than anything wrong inside the body. -/
meta def firstIllTyped? (td : TypeDecls) (nodes : Array (Syntax × Expression × Context)) :
    Option (Syntax × String) :=
  nodes.findSome? fun (stx, e, ctx) =>
    match e.inferE td ctx with
    | .ok _ => none
    | .error m => some (stx, m)

/-- Record the type of every expression of a declaration on the source it was written as, so that
hovering over any part of a DSL body shows the type that part has.

The same `nodes` and the same `inferE` the check reads, so the two cannot disagree about what a
subexpression's type is: what is shown is what was checked.  A node whose type `inferE` cannot find
is skipped — it is either the one being reported or a node under a splice — so a body with a mistake
in it still shows types for the parts that have them.

An expression nested in another is recorded over a range nested in the other's, and the hover of an
innermost node is what the editor shows, so the nesting needs nothing said about it here. -/
meta def addNodeTyInfo (td : TypeDecls) (nodes : Array (Syntax × Expression × Context)) :
    Elab.TermElabM Unit :=
  nodes.forM fun (stx, e, ctx) => do
    if let .ok t := e.inferE td ctx then
      addTyInfo stx t

elab_rules : term
  | `([lgtm| $e]) => do
      let (v, st) : Expression × LgtmElabState ←
        LgtmElabM.run' (report := false) (elabLgtmExpr [] e)
      return lgtmTerm v st

/-! ## Declarations -/

/-- The visibility of an `@[lgtm] def`.  `public` because a `module` hides even the names of its own
parser aliases otherwise, and this one is referred to by the command syntax below. -/
public syntax lgtmVis := "private "

/-- `@[lgtm] def f (x : int) : int := body` declares `f : FuncDecl`.

The IR name defaults to the Lean name; `as "f-name"` overrides it, which is what IR names that are
not Lean identifiers need.  A doc comment becomes the `FuncDecl.docstring` field as well as the Lean
declaration's own documentation.

The parameters are the `FuncDecl`'s parameter list and so are also the context its body is checked
in; they are not Lean binders.

`@[lgtm] private def` makes the generated Lean declaration `private`, and the visibility sits where
Lean's own declarations put it: `@[lgtm]` is the command's leading token, so what follows it is free
to be spelled the way the declaration it generates is. -/
syntax (docComment)? "@[lgtm] " (lgtmVis)? "def " ident (&"as" str)? ("(" ident " : " lgtmTy ")")*
  " : " lgtmTy " := " lgtmExpr : command

/-! ## What the commands do besides declare

A command has the two things needed to check what it is declaring: the declaration, and the syntax
every part of it came from.  So it checks it, and reports what it finds where the writer is looking
rather than leaving it to the module that collects the declarations — which in this development is
`LgtmDeepLean.Model.Tests`, at the top of the import graph, where nothing is reported until
everything has been built.

Three things happen after the Lean declaration is made:

1. the declaration is added to the scope, so that everything after it — here and in every module
   importing this one — can resolve its name;
2. unless something has already been reported about it, it is type checked against the declarations
   in scope with itself among them, and a failure is reported on its body; and
3. nothing, when the term contains a splice: a value with a splice marker in it is not the
   expression the writer wrote, so there is nothing to check it against.

The value the Lean declaration takes and the declaration this check is run on come out of one pass
over the body: `elabFuncDecl`, which the command runs for itself and which the `[lgtm_body| ...]`
term it generates for the value runs again with nothing reported.  They have to be one pass now that
a form reads by type — the brackets of `m[k]` are read by the very context the body is checked in, so
a value elaborated as a fragment would hold a lookup where the checked declaration had an index, and
the constant would be something nothing had reported on.

Step 2 is skipped after step 1 has reported a name nothing declares, because the type checker would
then report the same mistake a second time and less precisely — it reaches the name through the
expression around it, where the name itself is where the mistake is.

What this check is *not* is the authority.  It sees the declarations in scope, which is a prefix of
the program the proofs are about, so it reports nothing the whole-program check would not; the
reverse does not hold, and `Program.check` is still what `Model.Tests` runs.  See
`LgtmDeepLean.Lang.Syntax.Scope`. -/

/-- The Lean constant a command's `$n` declared, which is what a mention of the IR name points at.

Resolved rather than assembled from the current namespace, since a `private` declaration is stored
under a name that mangles the module it is in.  `none` if it cannot be found, which costs only the
navigation. -/
meta def resolveDeclName (n : Ident) : Elab.Command.CommandElabM (Option Name) := do
  try
    return some (← Elab.Command.liftCoreM <| Elab.realizeGlobalConstNoOverloadWithInfo n)
  catch _ =>
    return none

/-- A doc comment carrying `text`, for the generated Lean declaration to be documented with.

Assembled rather than written, because what it documents the declaration with is partly the
declaration itself: the signature of an `@[lgtm] def` is written in the DSL, and what a mention of it
hovers to is the Lean constant it generated — so the signature goes in the docstring of that
constant, where it is the one place an editor will show it.

The two characters that end a doc comment are spaced apart wherever they occur in `text`: the
signature is source text and a splice in it is a Lean term, which may contain anything. -/
meta def mkDocComment (text : String) : TSyntax ``Lean.Parser.Command.docComment :=
  let text := text.replace "-/" "- /"
  ⟨mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (text ++ "-/")]⟩

/-- The documentation the Lean declaration of an `@[lgtm] def` is given: its DSL signature as written,
and the doc comment it was written with under it.

The signature is the source text of the parameters and the result type rather than the `Ty`s they
elaborate to, so what is shown is what the writer wrote — `~(t)` included, where a rendered `Ty`
would show the splice's value or nothing at all.

`***` is the separator Lean's own hovers use between a signature and the documentation under it. -/
meta def declDocString (irName : String) (xs : Array Ident) (ts : Array (TSyntax `lgtmTy))
    (rt : TSyntax `lgtmTy) (docText : String) : String :=
  let src (stx : Syntax) : String := (stx.reprint.getD "").trimAscii.toString
  let ps := (xs.zip ts).toList.map fun (x, t) => s!" ({x.getId} : {src t})"
  let sig := s!"@[lgtm] def {irName}{String.join ps} : {src rt}"
  s!"```lgtm\n{sig}\n```" ++ if docText.isEmpty then "" else s!"\n***\n{docText}"

/-- The `FuncDecl` an `@[lgtm] def` denotes, together with the `TypeDecls` it was read against.

The body is elaborated under the context the declaration gives it — the parameters, every global's
type, and a provisional entry for the declaration itself, so that it may call itself — which is
exactly what `FuncDecl.check` puts in front of it.

One pass with two callers: the command, which reports and checks, and the `[lgtm_body| ...]` term it
generates as the value of the Lean declaration.  They have to be the same pass, and the two forms
whose `Expression` depends on a type — the brackets of `m[k]` and `map` — are why.  The type either
depends on is the one this context gives: a body elaborated as a fragment for the value would read
`xs[i]` over a `list int` parameter as the lookup a fragment has no choice but to read it as, and
`map m f` over a `hashmap string int` parameter as a list's mapping, and the Lean declaration would
then hold something other than what the command checked and reported on. -/
meta def elabFuncDecl (docstring : String) (irName : String) (leanName : Name) (xs : Array Ident)
    (ts : Array (TSyntax `lgtmTy)) (rt : TSyntax `lgtmTy) (body : TSyntax `lgtmExpr) :
    LgtmElabM (FuncDecl × TypeDecls) := do
  let parameters ← (xs.zip ts).toList.mapM fun (x, t) => do
    return (x.getId.toString, ← elabLgtmTy t)
  let resultType ← elabLgtmTy rt
  let self : FuncDecl :=
    { docstring, name := irName, parameters, resultType,
      body := .unreachable resultType "the declaration being elaborated" }
  let entry : LgtmEntry := { irName, leanName, decl := .fn self }
  withReader (fun ctx => { ctx with extra := ctx.extra.addEntry entry }) do
    -- The context the body is checked in, which is the one it is read in: the parameters and every
    -- global's type, exactly what `FuncDecl.check` puts in front of it.
    let ctx := parameters ++ Globals.types (← read).allGlobals
    let bodyExpr ← elabLgtmExpr ctx body
    return ({ self with body := bodyExpr }, (← read).allTypeDecls)

/-- `[lgtm_body| f "ir-name" (x : int) : int := e]` is the `Expression` that the body of that
`@[lgtm] def` denotes.

What it adds over `[lgtm| e]` is the context: a fragment has none, where this has the one the
declaration gives its body.  Generated by the command below as the value of the Lean declaration it
makes, and not meant to be written by hand — the Lean name and the IR name are both passed because
the body may mention the declaration itself.

Silent: it reports nothing and records nothing, since the command's own pass over the same body is
what does both. -/
syntax :max "[lgtm_body| " ident str ("(" ident " : " lgtmTy ")")* " : " lgtmTy " := "
  lgtmExpr "]" : term

elab_rules : term
  | `([lgtm_body| $n:ident $ir:str $[($xs:ident : $ts:lgtmTy)]* : $rt:lgtmTy := $b:lgtmExpr]) => do
      let ((d, _), st) : (FuncDecl × TypeDecls) × LgtmElabState ←
        LgtmElabM.run' (report := false) (elabFuncDecl "" ir.getString n.getId xs ts rt b)
      return lgtmTerm d.body st

elab_rules : command
  | `($[$doc:docComment]? @[lgtm] $[$vis:lgtmVis]? def $n:ident $[as $ir:str]?
        $[($xs:ident : $ts:lgtmTy)]* : $rt:lgtmTy := $body:lgtmExpr) => do
      let irName := (ir.map (·.getString)).getD n.getId.toString
      let docText := match doc with
        | some d => d.getDocString.trimAscii.toString
        | none => ""
      -- The Lean declaration: the value is what the quotations elaborate to, and the body's
      -- quotation is `[lgtm_body| ...]` rather than `[lgtm| ...]` so that it is the pass the check
      -- below runs — a fragment has no context, and one form is read by it.
      let ps ← (xs.zip ts).mapM fun (x, t) =>
        `(($(Lean.quote x.getId.toString), [lgtm_ty| $t]))
      let val ← `({ docstring := $(Lean.quote docText)
                    name := $(Lean.quote irName)
                    parameters := [$ps,*]
                    body :=
                      [lgtm_body| $n $(Lean.quote irName) $[($xs : $ts)]* : $rt := $body]
                    resultType := [lgtm_ty| $rt] : FuncDecl })
      -- The Lean declaration is documented with the DSL signature as well as with the doc comment,
      -- since a mention of the IR name hovers to this constant.
      let leanDoc := mkDocComment (declDocString irName xs ts rt docText)
      Elab.Command.elabCommand <| ←
        match vis with
        | some _ => `($leanDoc:docComment private def $n : FuncDecl := $val)
        | none => `($leanDoc:docComment def $n : FuncDecl := $val)
      let leanName := (← resolveDeclName n).getD n.getId
      -- The declaration again, as a value this time, with its name and its signature in scope for
      -- its body so that it may call itself.
      Elab.Command.liftTermElabM do
        let ((d, td), st) : (FuncDecl × TypeDecls) × LgtmElabState ←
          LgtmElabM.run' (report := true) (elabFuncDecl docText irName leanName xs ts rt body)
        addLgtmEntry { irName, leanName, decl := .fn d }
        addNodeTyInfo td st.nodes
        unless st.reported || !st.splices.isEmpty do
          let gs := (← getLgtmScope).globals
          match d.body.check td (d.parameters ++ Globals.types gs) d.resultType with
          | .ok _ => pure ()
          | .error m =>
              -- The declaration does not check, so something in it does not: report on the
              -- innermost part that does not, and on the body itself when the disagreement is
              -- between the body and the type declared for it.
              match firstIllTyped? td st.nodes with
              | some (stx, m') => logErrorAt stx m'
              | none => logErrorAt body m

/-- `@[lgtm, forward] def f (x : int) : int` says that `f` is declared further down, so that
something written before it may call it.

What it declares is a signature and nothing else: no Lean declaration is generated and nothing is
added to any `Program`, so the promise is kept by writing the `@[lgtm] def` itself, and broken by not
writing it — which `Program.check` is what catches, since a caller of something no program declares
is a caller of nothing.

`forward` is a second attribute rather than a word of its own between `@[lgtm]` and `def`, so that
the text stays shaped like the Lean attribute list it is spelled as.  Both words are written with
`&`, Lean's non-reserved form, since this is the one of the four commands whose leading token is
`@[` and not `@[lgtm]`.

This is the escape hatch for mutual recursion, which is the one thing checking a declaration where
it is written cannot do on its own: `ping` calling `pong` and `pong` calling `ping` means one of
them is written before the other is declared, and a table built as the declarations go by does not
have it yet. -/
syntax (docComment)? "@[" &"lgtm" ", " &"forward" "] " "def " ident (&"as" str)?
  ("(" ident " : " lgtmTy ")")* " : " lgtmTy : command

elab_rules : command
  | `($[$doc:docComment]? @[lgtm, forward] def $n:ident $[as $ir:str]?
        $[($xs:ident : $ts:lgtmTy)]* : $rt:lgtmTy) => do
      let irName := (ir.map (·.getString)).getD n.getId.toString
      let docText := match doc with
        | some d => d.getDocString.trimAscii.toString
        | none => ""
      Elab.Command.liftTermElabM do
        let (d, _) ← LgtmElabM.run' (report := true) do
          let parameters ← (xs.zip ts).toList.mapM fun (x, t) => do
            return (x.getId.toString, ← elabLgtmTy t)
          let resultType ← elabLgtmTy rt
          return ({ docstring := docText, name := irName, parameters, resultType,
                    body := .unreachable resultType "forward declaration" } : FuncDecl)
        addLgtmEntry { irName, leanName := n.getId, decl := .fn d }

/-- Fail at the first of `ns` that repeats a name an earlier one already used, saying so in terms of
`what` — "field", "constructor".

`StructDecl.fields` and `InductiveDecl.constructors` are both association lists read with
`List.lookup`, so an entry repeating a name is one nothing can reach: `StructDecl.FieldNamesUnique`
and `InductiveDecl.CtorNamesUnique` are the conditions saying so, and `Program.check` rejects a
declaration failing either.  Failing here as well is what keeps the surface syntax from writing one
at all, and it is the better place to say it: the error lands on the name that repeats rather than
on the program the declaration ends up in.

`meta` because it runs while the command elaborates rather than at run time. -/
meta def throwOnRepeatedName (what : String) (ns : Array Ident) :
    Elab.Command.CommandElabM Unit := do
  let mut seen : Array String := #[]
  for n in ns do
    let s := n.getId.toString
    if seen.contains s then
      throwErrorAt n s!"duplicate {what} `{s}`: a declaration names each {what} once"
    seen := seen.push s

/-- One field of an `@[lgtm] structure`: its name and its type.  `public` for the reason `lgtmVis`
is, and a parser alias of its own so that the fields can be written one to a line. -/
public syntax lgtmField := ident " : " lgtmTy

/-- The name and the type of one `lgtmField`, which is the one shape both passes over an
`@[lgtm] structure` read it in. -/
meta def lgtmFieldParts (f : TSyntax `lgtmField) :
    Elab.Command.CommandElabM (Ident × TSyntax `lgtmTy) := do
  match f with
  | `(lgtmField| $fn:ident : $t:lgtmTy) => return (fn, t)
  | _ => throwErrorAt f "not a field of an `@[lgtm] structure`"

/-- ```
@[lgtm] structure Point where
  x : int
  y : int
```
declares `Point : StructDecl`.

The same shape as `@[lgtm] def`: the IR name defaults to the Lean name and `as "point"` overrides
it, and `@[lgtm] private structure` makes the generated Lean declaration `private`.  The fields are
one to a line under the `where`, in the order they are written, which is the order a `new` has to
give them in.  A structure with no fields at all is the `where` and nothing after it.

The field list is `manyIndent`, so it ends where the indentation does: a line at or left of the
first field's column is the next command rather than a field of this one.

No two fields may share a name, which `StructDecl.FieldNamesUnique` is the condition for: a second
`x` is a field no `p.x` could read and no `{ p with x = ... }` could rebind, so it is an error here
rather than a declaration only `Program.check` would turn down.

A doc comment documents the Lean declaration only.  A `StructDecl` has no docstring field to put it
in, unlike a `FuncDecl`. -/
syntax (docComment)? "@[lgtm] " (lgtmVis)? "structure " ident (&"as" str)? " where "
  manyIndent(ppLine lgtmField) : command

elab_rules : command
  | `($[$doc:docComment]? @[lgtm] $[$vis:lgtmVis]? structure $n:ident $[as $ir:str]?
        where $[$fieldStxs:lgtmField]*) => do
      let parts ← fieldStxs.mapM lgtmFieldParts
      let fs := parts.map Prod.fst
      let ts := parts.map Prod.snd
      throwOnRepeatedName "field" fs
      let irName := (ir.map (·.getString)).getD n.getId.toString
      let fields ← (fs.zip ts).mapM fun (f, t) =>
        `(($(Lean.quote f.getId.toString), [lgtm_ty| $t]))
      let val ← `({ name := $(Lean.quote irName), fields := [$fields,*] : StructDecl })
      Elab.Command.elabCommand <| ←
        match vis with
        | some _ => `($[$doc:docComment]? private def $n : StructDecl := $val)
        | none => `($[$doc:docComment]? def $n : StructDecl := $val)
      let leanName := (← resolveDeclName n).getD n.getId
      -- The declaration's own name is in scope for its field types, so a struct may hold a value
      -- of itself: `@[lgtm] structure Tree where kids : list (struct Tree)` names something
      -- declared.
      Elab.Command.liftTermElabM do
        let (d, _) ← LgtmElabM.run' (report := true)
            (extra := LgtmScope.addEntry {}
              { irName, leanName, decl := .st { name := irName, fields := [] } }) do
          let fields ← (fs.zip ts).toList.mapM fun (f, t) => do
            return (f.getId.toString, ← elabLgtmTy t)
          return ({ name := irName, fields } : StructDecl)
        addLgtmEntry { irName, leanName, decl := .st d }

/-- One constructor of an `@[lgtm] inductive`: its name, and the types of the data it carries.  A
constructor that carries nothing takes no parentheses, which is what makes a plain enumeration look
like one. -/
public syntax lgtmCtor := ident ("(" lgtmTy,* ")")?

/-- ```
@[lgtm] inductive Color where
  | Red
  | Green
  | Rgb(int, int, int)
```
declares `Color : InductiveDecl`.

The same shape as `@[lgtm] structure`: the IR name defaults to the Lean name and `as "color"`
overrides it, and `@[lgtm] private inductive` makes the generated Lean declaration `private`.  The
constructors are one to a line under the `where`, each behind a `|`, in the order they are written,
which is the order a `match` has to give its alternatives in.  A type with no constructors at all is
the `where` and nothing after it.

A constructor's data has types but no names — it is taken apart by position — so a constructor is
written like a function type's parameter list rather than like a struct's fields.

No two constructors may share a name, which `InductiveDecl.CtorNamesUnique` is the condition for and
which is an error here for the reason a repeated field is: a second `Red` is one `new C.Red(...)`
could never build and one a `match` would have to write a second alternative for and never reach.

A doc comment documents the Lean declaration only.  An `InductiveDecl` has no docstring field to put
it in, as a `StructDecl` has not. -/
syntax (docComment)? "@[lgtm] " (lgtmVis)? "inductive " ident (&"as" str)? " where "
  manyIndent(ppLine "| " lgtmCtor) : command

/-- The name and the types of one `lgtmCtor`, which is the one shape both passes over an
`@[lgtm] inductive` read it in. -/
meta def lgtmCtorParts (c : TSyntax `lgtmCtor) :
    Elab.Command.CommandElabM (Ident × Array (TSyntax `lgtmTy)) := do
  match c with
  | `(lgtmCtor| $cn:ident $[($ts:lgtmTy,*)]?) => return (cn, (ts.map (·.getElems)).getD #[])
  | _ => throwErrorAt c "not a constructor of an `@[lgtm] inductive`"

elab_rules : command
  | `($[$doc:docComment]? @[lgtm] $[$vis:lgtmVis]? inductive $n:ident $[as $ir:str]?
        where $[| $cs:lgtmCtor]*) => do
      let parts ← cs.mapM lgtmCtorParts
      throwOnRepeatedName "constructor" (parts.map Prod.fst)
      let irName := (ir.map (·.getString)).getD n.getId.toString
      let ctors ← parts.mapM fun (cn, ts) => do
        let tys ← ts.mapM fun t => `([lgtm_ty| $t])
        `(($(Lean.quote cn.getId.toString), [$tys,*]))
      let val ← `({ name := $(Lean.quote irName), constructors := [$ctors,*] : InductiveDecl })
      Elab.Command.elabCommand <| ←
        match vis with
        | some _ => `($[$doc:docComment]? private def $n : InductiveDecl := $val)
        | none => `($[$doc:docComment]? def $n : InductiveDecl := $val)
      let leanName := (← resolveDeclName n).getD n.getId
      Elab.Command.liftTermElabM do
        let (d, _) ← LgtmElabM.run' (report := true)
            (extra := LgtmScope.addEntry {}
              { irName, leanName, decl := .ind { name := irName, constructors := [] } }) do
          let constructors ← parts.toList.mapM fun (cn, ts) => do
            return (cn.getId.toString, ← ts.toList.mapM elabLgtmTy)
          return ({ name := irName, constructors } : InductiveDecl)
        addLgtmEntry { irName, leanName, decl := .ind d }
