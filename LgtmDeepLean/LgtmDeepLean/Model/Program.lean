module

public import LgtmDeepLean.Model.Basic
public import LgtmDeepLean.Model.Basic.WellFormed
public import LgtmDeepLean.Model.CommentThreads.Operations
public import LgtmDeepLean.Model.CommentManager.Operations
public import LgtmDeepLean.Model.Location.Operations
public import LgtmDeepLean.Model.Files.Operations

/-! # The model as one program

The model is written across modules, one subject to a module, but the type checker and the
relational semantics are both stated about a `Program`: one table of types and one table of globals
that every body is checked and run against.  `modelProgram` is that `Program` — the model's
declarations, all of them, collected into the artifact the rest of the language is about.

This is not where anything is checked; `LgtmDeepLean.Model.Tests` is.  Collecting the declarations
and running the checker over them are separate so that a caller wanting the model as a `Program` —
to evaluate a call, to state a theorem about a declaration under the globals it is really checked
against — does not import a module of tests to get it.

## Adding a module

A new `LgtmDeepLean/Model/Foo.lean` joins the model in two steps:

1. In `Foo.lean`, list what it declares as `Model.Foo.structDecls`, `Model.Foo.inductiveDecls` and
   `Model.Foo.funcDecls`, leaving out the lists for kinds it declares none of.
2. Here, `public import` it and append its lists to the fields below.

Nothing in `Model.Tests`, which checks `modelProgram`, and nothing in `Model.WellTyped`, whose
theorem runs that same check: both are about whatever this is, and neither names a declaration.  A
new struct that a well-formedness predicate is stated about does belong in `Model.Declares`, which
is the one place a name is written down twice.

Appending rather than keying by name is deliberate.  `Program` is a list per kind and the tables are
derived from it by `Program.globals` and friends; whether two modules declared the same name twice
is then a condition on the program, which is what `Model.Tests` decides rather than something this
assembly could quietly resolve. -/

@[expose] public section

/-- Every declaration of the model, under the tables they are all checked and run against.

The order is the order the modules are imported in and, within a module, the order its lists are
written in.  Order means nothing to the type checker — every body is checked against all of the
globals, its own and those declared after it alike — but extraction preserves it, so it is the
declaration order of the model and worth keeping stable. -/
def modelProgram : Program where
  structDecls := Model.Basic.structDecls
  inductiveDecls := Model.Basic.inductiveDecls
  funcDecls := Model.Basic.funcDecls ++ Model.CommentThreads.funcDecls ++ Model.CommentManager.funcDecls ++ Model.Location.funcDecls ++ Model.Files.funcDecls

/-- The model's table declares the model's structs.

What `Model.Declares` is a hypothesis about, discharged for the one table it is really wanted of.
Every step from `modelProgram` to a struct declaration is a projection or a `List.lookup` over a
literal list, all of them exposed, so each clause holds by `rfl` — the table is not computed, it is
the declarations written down. -/
theorem Model.declares_modelProgram : Model.Declares modelProgram.typeDecls := ⟨rfl, rfl, rfl, rfl⟩

end
