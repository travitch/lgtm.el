module

import LgtmDeepLean.Model.Program
meta import LgtmDeepLean.Model.Program
meta import Lean

/-! # The type checker run over the model

The driver for the model: every declaration the model makes, checked against the tables all of them
are checked against.  It runs at build time — a `#guard` that fails is a build error — so a
declaration the checker turns down cannot be committed, and neither can one that two modules
declare under the same name.

Three things are checked, and the third is why the first two keep covering the model as it grows:

1. Every declaration type checks, which is `Program.check`.
2. No two declarations share a name, which `Program.check` says nothing about: a name declared twice
   is a condition across declarations rather than anything a body could be wrong about.
3. Every IR declaration the model's modules define is one `modelProgram` collects.  Without this the
   first two would still pass over a model a module had quietly stopped contributing to.

Nothing here mentions a module of the model, so a module added to `modelProgram` is checked by all
three without this one changing. -/

/-! ## Every declaration type checks

`Program.check` runs `Expression.infer` over each declaration's body in the context of its own
parameters and the signatures of every global, and also decides the two conditions on declared types
that no expression could be wrong about: no structure type repeats a field name, no inductive type
repeats a constructor.

`#guard` rather than `by decide`: `Expression.infer` is not exposed, so the kernel cannot reduce the
application, where `#guard` evaluates it compiled.  Which is the same reason this module takes a
`meta import` of the model as well as a plain one — the `#guard` runs the model's declarations as
code at elaboration time. -/

#guard modelProgram.check

/-! ## No two declarations share a name

One condition per kind of declaration, each a `Nodup` over the names declared, and each decided by
the kernel: these are about the names in the lists, not about anything a body says.

These are what make a declaration of the model callable — `Program.lookup_self` and its two
counterparts turn "`d` is one of the program's declarations" into "`d` is what its own name
resolves to", which is what carries `Program.WellTyped` down to a particular declaration. -/

example : modelProgram.NamesUnique := by decide
example : modelProgram.StructNamesUnique := by decide
example : modelProgram.InductiveNamesUnique := by decide

/-! ## Every declaration is one `modelProgram` collects

`lgtm` builds one Lean constant per IR declaration and nothing that collects them, so what
`modelProgram` contains is what the per-module lists say it contains, and a declaration left out of
those lists is one the checks above never see.  What follows is the check against that: the IR
declarations the model's modules define, against the ones `modelProgram` reaches.

Both sides are read off the environment rather than written down, which is the point — a module
added to the model is covered by this as it stands.  The one thing it cannot see is a module
`Model.Program` does not import at all: its constants are not in this environment either.  That is
the import in step 2 of `Model.Program`'s instructions, and the reason the step exists. -/

open Lean

/-- Whether `c` was defined in one of the model's modules.  `none` is a constant defined in this
module, which is not one of them. -/
private meta def isModelConst (env : Environment) (c : Name) : Bool :=
  match (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]! with
  | some m => (`LgtmDeepLean.Model).isPrefixOf m
  | none => false

/-- Every IR declaration the model's modules define.

A constant of type `StructDecl`, `InductiveDecl` or `FuncDecl` is what each `lgtm` command builds
exactly one of, so these are the declarations of the model found the way the model writes them,
independently of any list that claims to collect them. -/
private meta def modelIrDecls (env : Environment) : Array Name := Id.run do
  let mut out := #[]
  for i in [0:env.header.moduleNames.size] do
    if (`LgtmDeepLean.Model).isPrefixOf env.header.moduleNames[i]! then
      out := out ++ env.header.moduleData[i]!.constNames.filter fun c =>
        match env.find? c with
        | some ci => [``StructDecl, ``InductiveDecl, ``FuncDecl].any ci.type.isConstOf
        | none => false
  return out

/-- The model constants `root`'s definition mentions, each one found followed into its own
definition: `modelProgram` mentions the per-module lists, and those mention the declarations.

Expansion stops at anything outside the model's modules.  `List.cons` and the IR constructors are
how a list of declarations is written rather than somewhere a declaration could be, so following
them would only walk the library. -/
private meta partial def mentionedUnder (env : Environment) (seen : NameSet) (root : Name) :
    NameSet :=
  if seen.contains root || !isModelConst env root then seen
  else
    let seen := seen.insert root
    match (env.find? root).bind ConstantInfo.value? with
    | some v => v.getUsedConstants.foldl (init := seen) (mentionedUnder env)
    | none => seen

/-- The IR declarations of the model that `root` does not reach. -/
private meta def unlistedUnder (root : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let listed := mentionedUnder env {} root
  return (modelIrDecls env).filter fun c => !listed.contains c

run_meta do
  let missing ← unlistedUnder ``modelProgram
  unless missing.isEmpty do
    Lean.throwError m!"the model declares {missing.size} declaration(s) that `modelProgram` does \
      not collect, so nothing type checks them: {missing}.\n\nAdd each to the list for its kind in \
      the module that declares it, and the module's lists to `modelProgram` — see the \
      \"Adding a module\" section of `LgtmDeepLean.Model.Program`."

/-! The check above is not vacuous: run from one of the lists instead of from `modelProgram`, it
reports the declarations the other lists contribute — which is also what it would report of a
`modelProgram` that had stopped reading one of them. -/

run_meta do
  if (← unlistedUnder ``Model.Basic.structDecls).isEmpty then
    Lean.throwError "the completeness check above reports nothing even run over one list of \
      declarations, so it would report nothing over a `modelProgram` missing a whole module"
