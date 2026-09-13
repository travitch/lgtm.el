This package implements a code review UI for emacs.

-The implementation is mostly in elisp.
- The LgtmLean directory contains a formalization of the core data structures and operations in Lean


# Development Guidelines

- Build the Lean project using `lake build`
- Use only dependencies in core lean and the lean standard library
- Use the lean-lsp-mcp server to search for Lean theorems and functions
- Use the lean-lsp-mcp server to interact with the project where necessary
- Run `lake test` to validate that the end-to-end regression tests pass
