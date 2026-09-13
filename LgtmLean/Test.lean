import Extractor

/-- Runs the full extraction pipeline over `LgtmLean` and fails (non-zero exit code) if it produced
any `opaqueValues` -- each one marks an `LExpr.opaque` that `SExpr.toSExpr` (`Render.lean`) had to
render as a runtime `(error ..)` placeholder instead of translating properly, which would otherwise
land silently in the generated elisp as broken code. -/
unsafe def main : IO UInt32 := do
  let (_translations, _rendered, postState) ← extractLgtm
  if postState.opaqueValues.isEmpty then
    pure 0
  else
    IO.eprintln s!"extraction produced {postState.opaqueValues.length} opaque value(s):"
    for reason in postState.opaqueValues.reverse do
      IO.eprintln s!"  - {reason}"
    pure 1
