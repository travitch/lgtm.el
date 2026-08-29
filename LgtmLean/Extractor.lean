import Lean
import LgtmLean

open Lean

/-- Whether `name` originates from the `LgtmLean` library.

Under Lean's module system, a declaration that isn't explicitly marked `public` is compiled as
module-private and stored under a mangled name of the form `_private.<Module>.<n>.<OriginalName>`
(e.g. `_private.LgtmLean.Threads.0.CommentThreads.nextCommentInThread`), which no longer looks like
it lives under `LgtmLean` at all. Genuinely `public` declarations (like the ones in `Tree.lean`)
keep their plain, unmangled name instead, so those have to be attributed via the environment's own
module index. -/
def isLgtmLeanDecl (env : Environment) (name : Name) : Bool :=
  if (toString name).startsWith "_private.LgtmLean." then
    true
  else
    match env.getModuleIdxFor? name with
    | none => false
    | some modIdx =>
      let modName := env.header.modules[modIdx.toNat]!.module
      modName == `LgtmLean || (`LgtmLean).isPrefixOf modName

/-- Whether `info` is an ordinary function definition, as opposed to a theorem, axiom, structure,
inductive, constructor, recursor, or other kind of declaration. -/
def isFunctionDecl : ConstantInfo → Bool
  | .defnInfo _ => true
  | _ => false

/-- Whether `name` is a declaration the compiler generated on our behalf (structure/inductive
machinery, equation lemmas, proof-irrelevant subterms, etc.) rather than something a person wrote.

Deliberately only inspects `name`'s own last component, not `Name.isInternalDetail` (which also
inspects the *prefix* for numeric components) -- under the module system, an ordinary
(non-`public`) declaration is itself stored with a numeric component in its prefix (see
`isLgtmLeanDecl`), which would make `isInternalDetail` flag every such declaration as generated. -/
def isCompilerGenerated (env : Environment) (name : Name) : Bool :=
  let hasBadLastComponent :=
    match name with
    | .str _ s =>
      s == "ctorIdx" || s == "ctorElimType" || s.startsWith "_" || s.startsWith "eq_" ||
        s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "omega_" ||
        s.endsWith "_flat_ctor" || s.startsWith "sizeOf_spec" || s.endsWith "noConfusionType" ||
        s.startsWith "inst"
    | _ => true
  -- Catches instance-dictionary field projections (e.g. `instBEqFoo.beq`) and `match_N.splitter`
  -- helpers, whose *own* last component looks ordinary but whose parent doesn't.
  let hasBadParentComponent :=
    match name.getPrefix with
    | .str _ s => s.startsWith "inst" || s.startsWith "match_"
    | _ => false
  Lean.isAuxRecursor env name || Lean.isNoConfusion env name || env.isProjectionFn name ||
    Lean.Meta.isInstanceCore env name || hasBadLastComponent || hasBadParentComponent

def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `LgtmLean }] {} (trustLevel := 1024)
  let names := env.constants.toList.filterMap fun (name, info) =>
    if isFunctionDecl info && isLgtmLeanDecl env name && !isCompilerGenerated env name then
      some name
    else
      none
  let sorted := names.map toString |>.mergeSort (· ≤ ·)
  for name in sorted do
    IO.println name

/-

# Overall design of the extractor

The extractor traverses function and type definitions to render them as elisp functions and definitions.

- All of the extracted functions will be private/internal elisp (i.e., prefixed with lgtm--)
- The extractor will maintain a list of names deemed public and to be prefixed with `lgtm-` to denote that they are available for users of the lgtm library
- No values or definitions in `Prop` will be exported, as they have no run-time representation
- Translation of functions will go through a simplified intermediate AST

-/
