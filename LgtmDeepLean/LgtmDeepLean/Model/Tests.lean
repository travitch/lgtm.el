module

import LgtmDeepLean.Model.Program
meta import LgtmDeepLean.Model.Program
meta import Lean

/-! # The type checker run over the model

Checks three things:

1. Every declaration type checks.
2. Declaration names are unique
3. All declarations in the model are included in the program (using metaprogramming)

-/

/-! ## Every declaration type checks -/

#guard (modelProgram.check).isOk

/-! ## No two declarations share a name -/

example : modelProgram.NamesUnique := by decide
example : modelProgram.StructNamesUnique := by decide
example : modelProgram.InductiveNamesUnique := by decide

/-! ## Every declaration is one `modelProgram` collects

Use metaprogramming to ensure that there are no definitions that were elided
from the program declaration. -/

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
