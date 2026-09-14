import Std
import Extractor


/-- Runs the full extraction pipeline over `LgtmLean` and fails (non-zero exit code) if it produced
any `opaqueValues` -- each one marks an `LExpr.opaque` that `SExpr.toSExpr` (`Render.lean`) had to
render as a runtime `(error ..)` placeholder instead of translating properly, which would otherwise
land silently in the generated elisp as broken code. -/
unsafe def main : IO UInt32 := do
  let (_translations, _rendered, postState) ← extractLgtm
  let definedSet := Std.HashSet.ofList postState.definedFunctionNames
  let undefinedCalledFuncs := postState.referencedGlobalNames.diff definedSet
  if postState.opaqueValues.isEmpty ∧ undefinedCalledFuncs.isEmpty then
    pure 0
  else
    IO.eprintln s!"Extraction produced {postState.opaqueValues.length} opaque value(s):"
    for reason in postState.opaqueValues.reverse do
      IO.eprintln s!"  - {reason}"
    IO.eprintln s!"Extraction produced {undefinedCalledFuncs.size} calls to functions that were not defined"
    for func in undefinedCalledFuncs.toList do
      IO.eprintln s!"  - {func}"
    pure 1
