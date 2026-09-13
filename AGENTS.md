The lgtm.el library implements a code review interface for emacs.

The LgtmLean subdirectory contains a formalization of the core data structures and operations for lgtm in Lean 4.

# Development Guidelines

- The project builds with `lake build`.
- Do not use functions or theorems from Mathlib, as the project does not want to take a dependency on mathlib.
- Run experiments in /tmp. Do not modify the modules in the project directory without confirmation.
- Prefer using standard UNIX tools to edit files compared to using e.g., python scripts
- Run `lake test` to validate that the end-to-end regression tests pass

