module

public import LgtmDeepLean.Lang.IR
public import Lean

/-! # The IR as Lean terms

`ToExpr` for each of the IR's data types, which is what lets an elaborator that has built a value —
a `Ty`, an `Expression`, a whole `FuncDecl` — emit the Lean declaration holding it.

This is the half of `LgtmDeepLean.Lang.Syntax` that runs backwards.  The elaborators there read
surface syntax into values rather than into syntax for values, so that the same pass that builds a
declaration can check it; what the generated `def` is then defined to be comes from here.  What
comes out is a constructor application, the same term the macros used to expand to, so nothing
downstream can tell which route a declaration arrived by: `decide` still reduces it and `@[expose]`
still unfolds it.

Imported `meta` by the module that elaborates the syntax, which is why `Lean` is imported publicly:
a `ToExpr` instance is of no use to a macro it is hidden from. -/

deriving instance Lean.ToExpr for Ty
deriving instance Lean.ToExpr for StructDecl
deriving instance Lean.ToExpr for InductiveDecl
deriving instance Lean.ToExpr for Expression
deriving instance Lean.ToExpr for FuncDecl
