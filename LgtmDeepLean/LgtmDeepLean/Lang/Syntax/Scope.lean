module

public import LgtmDeepLean.Lang.IR
public import LgtmDeepLean.Lang.TypeCheck
public import Lean

/-! # The declarations in scope

What an `lgtm` command needs to know to check the declaration it is elaborating: every declaration
the surface syntax has made so far, under the name it made it.  `Program.check` reads that table off
a `Program`, which is assembled in Lean from the declarations and so exists only downstream of all
of them; this is the same table accumulated as the declarations go by, so a command can check its
own declaration where it is written instead of waiting for a module that collects it.

## What is in scope

The entries of every module imported, in import order, followed by the entries of the current module
in the order its commands appear.  That order is the whole reason this is worth stating: `Globals`,
`Structs` and `Inductives` are association lists read with `List.lookup`, which takes the first
entry for a name, so a table built in declaration order and extended at the end can never change a
lookup that already succeeded.  The table a declaration is checked against here is a prefix of the
one `modelProgram` presents (`LgtmDeepLean.Model.Program` appends its modules' lists in import
order), and therefore:

* a declaration that *type checks* here type checks there as well: the inline type check turns down
  nothing `Program.check` would have accepted; and
* a declaration that mentions something declared *after* it fails here and would have passed there,
  which is why `LgtmDeepLean.Model.Tests` keeps checking the whole program rather than trusting
  this, and why `lgtm forward` exists for the one case that needs it — two declarations that call
  each other.

Declaring something before it is used is what the model does anyway, so the second case is a
convention rather than a restriction.

The *names* are a different matter, and the prefix argument says nothing about them: resolving them
checks things `Program.check` does not look at, since it checks the bodies of declarations and so
never asks whether a struct's field type names a type anything declares.  Two of the mistakes the
model had in it when this was written were of exactly that kind.  So the inline pass is not merely
an earlier copy of the whole-program check; it is also the only thing that looks at some of this.

## Why an environment extension

A persistent extension is loaded from an ordinary `import`, so a module gets the declarations of
everything it imports with no bookkeeping of its own.  That is also what lets the surface syntax
stop asking about Lean names: `Foo.bar` is one IR name rather than a field read when *the IR* has a
declaration called `Foo.bar`, which this answers directly, where the Lean-name test it replaces
needed every model module to `meta import` the modules it called. -/

open Lean

/-- One declaration an `lgtm` command has made, under whichever of the IR's three kinds it is. -/
public inductive IrDecl where
  | st (d : StructDecl)
  | ind (d : InductiveDecl)
  | fn (d : FuncDecl)

/-- One entry of the scope: a declaration, the IR name it was made under, and the Lean constant the
command generated for it.

The Lean name is what makes a mention of an IR name navigable: it is what goto-definition on a call
inside a DSL body follows.  See `addIrNameInfo` in `LgtmDeepLean.Lang.Syntax`. -/
public structure LgtmEntry where
  irName : String
  leanName : Name
  decl : IrDecl

/-- The declarations in scope, as the tables that read them.

`entries` is the whole of the state and the other three are derived from it, kept alongside so that
a lookup is a lookup rather than a walk with a `match` in it.  All four are in declaration order. -/
public structure LgtmScope where
  entries : List LgtmEntry := []
  structs : Structs := []
  inductives : Inductives := []
  globals : Globals := []
  deriving Inhabited

/-- `s` with `e` added at the end, which is where a new declaration goes: appending is what keeps
every lookup that already succeeded answering what it did. -/
public def LgtmScope.addEntry (s : LgtmScope) (e : LgtmEntry) : LgtmScope :=
  let s := { s with entries := s.entries ++ [e] }
  match e.decl with
  | .st d => { s with structs := s.structs ++ [(e.irName, d)] }
  | .ind d => { s with inductives := s.inductives ++ [(e.irName, d)] }
  | .fn d => { s with globals := s.globals ++ [(e.irName, d)] }

/-- The type declarations in scope, as the one bundle everything that resolves a type name takes. -/
public def LgtmScope.typeDecls (s : LgtmScope) : TypeDecls where
  ss := s.structs
  is := s.inductives

/-- The entry declaring `irName`, whichever kind it is, or `none` if nothing declares it. -/
public def LgtmScope.find? (s : LgtmScope) (irName : String) : Option LgtmEntry :=
  s.entries.find? fun e => e.irName == irName

/-- Every IR name in scope, for suggesting the one that was meant. -/
public def LgtmScope.names (s : LgtmScope) : List String :=
  s.entries.map LgtmEntry.irName

public initialize lgtmScopeExt : SimplePersistentEnvExtension LgtmEntry LgtmScope ←
  registerSimplePersistentEnvExtension {
    addEntryFn := LgtmScope.addEntry
    addImportedFn := mkStateFromImportedEntries LgtmScope.addEntry {}
  }

/-- The declarations in scope here. -/
public def getLgtmScope [Monad m] [MonadEnv m] : m LgtmScope := do
  return lgtmScopeExt.getState (← getEnv)

/-- Add `e` to the scope of everything after it, and of every module importing this one. -/
public def addLgtmEntry [Monad m] [MonadEnv m] (e : LgtmEntry) : m Unit :=
  modifyEnv fun env => lgtmScopeExt.addEntry env e

/-! ## Suggesting the name that was meant

A mention of a name nothing declares is usually a name that *is* declared, spelled wrong or renamed
out from under its callers.  The scope has every name, so saying which one it looks like costs a
walk over a few dozen strings. -/

/-- The edit distance between `a` and `b`, capped at `limit`: how many single-character
insertions, deletions and substitutions turn one into the other.

Capped because the answer is only wanted when it is small, and a cap is what keeps the table
narrow. -/
public def editDistance (a b : String) (limit : Nat) : Nat :=
  let as := a.toList.toArray
  let bs := b.toList.toArray
  if as.size + limit < bs.size || bs.size + limit < as.size then limit + 1 else
  let row : Array Nat := (Array.range (bs.size + 1))
  Id.run do
    let mut prev := row
    for i in [1 : as.size + 1] do
      let mut cur : Array Nat := #[i]
      for j in [1 : bs.size + 1] do
        let sub := prev[j - 1]! + (if as[i - 1]! == bs[j - 1]! then 0 else 1)
        let del := prev[j]! + 1
        let ins := cur[j - 1]! + 1
        cur := cur.push (min sub (min del ins))
      prev := cur
    return prev[bs.size]!

/-- The name among `candidates` that `name` is most likely a misspelling of, if any is close
enough.

"Close enough" is a quarter of the name's length, at least one and at most six: a short name has
few spellings a typo could reach, while a long one is mostly its own evidence, and the mistake a
long name is likely to have is a rename rather than a typo — `sortThreads` for `sortThreadLists` is
four edits apart and the same name. -/
public def closestName? (name : String) (candidates : List String) : Option String :=
  let limit := max 1 (min 6 (name.length / 4))
  let scored := candidates.filterMap fun c =>
    let d := editDistance name c limit
    if d ≤ limit then some (d, c) else none
  match scored with
  | [] => none
  | p :: ps => some (ps.foldl (fun best q => if q.1 < best.1 then q else best) p).2

/-- `message`, with "did you mean `x`?" after it when `name` looks like a misspelling of something
in scope. -/
public def withSuggestion (name : String) (candidates : List String) (message : String) : String :=
  match closestName? name candidates with
  | some c => s!"{message}; did you mean '{c}'?"
  | none => message
