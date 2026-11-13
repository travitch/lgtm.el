module

public import LgtmDeepLean.Model.Program

/-! # The model type checks, as a theorem

`LgtmDeepLean.Model.Tests` already runs `Program.check` over `modelProgram` and fails the build if
it does not check.  That is a diagnostic: it names the declaration and says what about it, which is
what someone who has just broken a body wants to read.  What it does not leave behind is a *fact* —
`run_meta` proves nothing — so every theorem about a call into the model had to carry
`modelProgram.WellTyped` as a hypothesis, and nothing could discharge it.  This module is that fact,
and the two are complementary: the meta check is the diagnostic, this is the proof term.

It is one `rfl`.  `Program.check` is a function of the program and `modelProgram` is a literal, so
the kernel runs the type checker over the model the same way it evaluates any other closed term, and
`Program.wellTyped_of_check` reads the result as the judgement.  Nothing here mentions a declaration
by name, which is the point: a declaration added to the model is covered by this file without it
being touched.

So the inversion principles for `Expression.infer` are not what this goes through.  They are for
proofs *about* an expression's type, where the expression is a variable or the context is not a
literal and there is nothing to evaluate; here both are given, and evaluation is cheaper than any
rewriting would be — the whole check costs about two seconds.

What that cost is one attribute per definition the checker runs through: `Ty.beq`/`Ty.beqList`,
`Ty.common`, `Except.ofOption`/`expect`/`expectAll` with `Ty.firstMismatch`, `Expression.inferE`
and its three companions, `Expression.infer`, `Expression.check`, `Globals.types`,
`FuncDecl.check`, `Globals.checkEach` and `Globals.check`, up to `Program.check` itself.  A
non-exposed body does not reduce outside the module that defines it, and the error when one does not
names it, so the set is exactly what the checker touches on the path a well-typed program takes.
The seven message helpers those bodies name on their error branches had to become `public` with
them — an exposed body may not mention a private declaration — but not exposed: nothing reduces a
message where nothing goes wrong. -/

public section

/-- The model checks: every declaration type checks under the tables they are all checked against,
no structure declares a field twice, and no inductive declares a constructor twice.

Named rather than written at each use, so that the kernel runs the checker once and the three
theorems that read this answer share the one reduction. -/
theorem modelProgram.check_eq_ok : modelProgram.check = .ok () := rfl

/-- Every declaration of the model is well typed. -/
theorem modelProgram.wellTyped : modelProgram.WellTyped :=
  Program.wellTyped_of_check modelProgram.check_eq_ok

/-- No structure declaration of the model repeats a field name — which `Program.WellTyped` says
nothing about, and which every field read by name depends on. -/
theorem modelProgram.fieldNamesUnique : modelProgram.FieldNamesUnique :=
  Program.fieldNamesUnique_of_check modelProgram.check_eq_ok

/-- And no inductive declaration repeats a constructor name. -/
theorem modelProgram.ctorNamesUnique : modelProgram.CtorNamesUnique :=
  Program.ctorNamesUnique_of_check modelProgram.check_eq_ok

/-! ## What it buys

Preservation for the model, with no typing hypothesis left over.  `Program.Apply.hasType` wants
three things: the call, that the program checks, and which declaration the name resolves to.  The
first is the caller's; the second is `modelProgram.wellTyped`; the third is `rfl`, because
`Program.lookup` reads a literal table.  So a call into the model returns a value of the type the
declaration it called declares, for every argument list and without the caller proving anything
about the model. -/

/-- Whatever `CommentThreads.toThreadsOrdered` returns is a list of `CommentThread`s. -/
theorem CommentThreads.toThreadsOrdered.apply_hasType {args : List Value} {v : Value}
    (h : modelProgram.Apply "CommentThreads.toThreadsOrdered" args v) :
    v.HasType modelProgram.typeDecls (.list (.struct "CommentThread")) :=
  h.hasType modelProgram.wellTyped rfl

/-- And whatever `CommentManager.get` returns is an optional `Comment`. -/
theorem CommentManager.get.apply_hasType {args : List Value} {v : Value}
    (h : modelProgram.Apply "CommentManager.get" args v) :
    v.HasType modelProgram.typeDecls (.option (.struct "Comment")) :=
  h.hasType modelProgram.wellTyped rfl

end
