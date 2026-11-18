module

public import Lean.Meta.Tactic.Simp.Attr
meta import Lean.Meta.Tactic.Simp.RegisterCommand

/-! # Simp sets

The named `simp` sets this development gathers lemmas in.  A set has to be declared in a module of
its own: `register_simp_attr` expands to an `initialize`, and the extension it sets up exists only
once the module declaring it has been imported, so a set cannot be used in the file that declares
it. -/

/-- The walk `Env.lookup` takes through an environment a call built, as rewrites: the bindings a
`FuncDecl.callEnv` or an `Env.extend` puts in front, and the name-by-name search through them.

What this set is for is the side conditions a proof about a declaration leaves everywhere — that the
body's environment binds this parameter to this value, that it does not shadow that global.  They
are discharged by rewriting rather than by unfolding `Env.lookup` into `List.lookup`'s `if`-chains,
which is what keeps a lookup under a symbolic argument from turning into a case split. -/
register_simp_attr lgtm_env
