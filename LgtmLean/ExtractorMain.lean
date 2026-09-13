import Extractor

/-- CLI entry point for the `extractor` executable, kept in its own module (rather than in
`Extractor.lean` itself) so other executables -- e.g. `Test.lean` -- can import `Extractor` for
`extractLgtm` without colliding with this `main`, since Lean requires every declaration's fully
qualified name to be unique across the whole import closure. -/
unsafe def main (args : List String) : IO Unit := do
  let targetFile ← if hArgs : args.length ≠ 1 then
      throw (IO.userError "The path to an elisp file to generate is a required argument")
    else
      pure (System.FilePath.mk (args[0]'(by omega)))

  let (translations, rendered, _) ← extractLgtm

  renderIntermediate (System.FilePath.mk "/tmp/out.txt") translations
  renderToFile targetFile rendered
