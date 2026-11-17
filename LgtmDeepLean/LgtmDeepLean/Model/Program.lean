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
new struct that a well-formedness predicate is stated about does belong in `Model.DeclaresTypes`,
and a new declaration that a theorem about a call names belongs in `Model.Declares` below — those
are the one place a name is written down twice.

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

/-- The tables a theorem about a call into the model is read against: the model's structs under the
model's names, and the model's declarations under theirs.

`Model.DeclaresTypes` is the first half, extended here rather than restated because the two are
wanted in different places.  A lemma reading a field type calls nothing and takes the parent
(`CommentManager.hasType_get?` and the two beside it); a theorem about a call needs both, since a
body calls another declaration by *mentioning its name* and a `varRef` resolves through the globals
table the body is run under (`FuncDecl.apply_of_eval_app`) — nothing ties the name a body writes to
the `FuncDecl` this module collected, and a table holding something else under
`"CommentManager.get"` runs a different program.  So the clauses below are the other half of what it
means for a table to be the model's, and this is the one hypothesis that says it.

Bundled because unbundled it is a line per name in every signature, which is what it was.  The cost
is that a theorem taking this asks for every name in it, including those its own proof never calls;
it comes to nothing where the tables are the model's, which is where they are really wanted, and
`Model.declares_modelProgram` discharges every clause at once.  A theorem that wants to be read
against an arbitrary table can still take the single lookup it needs — the clauses are projections,
so `hDeclares.get` is what it is passed, and `hDeclares.toDeclaresTypes` is what a lemma asking for
the parent gets.

Clauses arrive as the theorems that read a struct or call a name arrive. -/
structure Model.Declares (td : TypeDecls) (gs : Globals) : Prop extends Model.DeclaresTypes td where
  get : gs.lookup "CommentManager.get" = some CommentManager.get
  asAlist : gs.lookup "CommentThreads.asAlist" = some CommentThreads.asAlist
  sortThreadLists : gs.lookup "CommentThreads.asAlist.sortThreadLists" =
    some CommentThreads.asAlist.sortThreadLists
  linearize : gs.lookup "CommentThread.linearize" = some CommentThread.linearize

/-- The model's tables are the model's: what `Model.Declares` is a hypothesis about, discharged for
the one pair of tables it is really wanted of.

Every step from `modelProgram` to a declaration is a projection, a `List.map` or a `List.lookup`
over a literal list, all of them exposed, so each clause holds by `rfl` — the tables are not
computed, they are the declarations written down. -/
theorem Model.declares_modelProgram :
    Model.Declares modelProgram.typeDecls modelProgram.globals :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩

end
