import Lean
import LgtmLean

import Extractor.Attribute
import Extractor.IR
import Extractor.Render
import Extractor.TopologicalSort

open Lean

/-

# Overall design of the extractor

The extractor traverses function and type definitions to render them as elisp functions and definitions.

- All of the extracted functions will be private/internal elisp (i.e., prefixed with lgtm--)
- Declarations tagged `@[public_api]` (see `Extractor/Attribute.lean`) are instead prefixed with
  `lgtm-` to denote that they are available for users of the lgtm library
- No values or definitions in `Prop` will be exported, as they have no run-time representation
- Translation of functions will go through a simplified intermediate AST

-/

/-- Whether `name` originates from the `LgtmLean` library.

Under Lean's module system, a declaration that isn't explicitly marked `public` is compiled as
module-private and stored under a mangled name of the form `_private.<Module>.<n>.<OriginalName>`
(e.g. `_private.LgtmLean.Threads.0.CommentThreads.nextCommentInThread`), which no longer looks like
it lives under `LgtmLean` at all. Genuinely `public` declarations (like the ones in `Tree.lean`)
keep their plain, unmangled name instead, so those have to be attributed via the environment's own
module index. -/
def isLgtmLeanDecl (env : Environment) (name : Name) : Bool :=
  if (toString name).startsWith "_private.LgtmLean." then
    true
  else
    match env.getModuleIdxFor? name with
    | none => false
    | some modIdx =>
      let modName := env.header.modules[modIdx.toNat]!.module
      modName == `LgtmLean || (`LgtmLean).isPrefixOf modName

/-- Whether `info` is an ordinary function definition, as opposed to a theorem, axiom, structure,
inductive, constructor, recursor, or other kind of declaration. -/
def isFunctionDecl : ConstantInfo → Bool
  | .defnInfo _ => true
  | _ => false

/-- Test if `name` is a structure definition.

Structures happen to be defined as inductives with one constructor and projection functions for its
fields, so we have to inspect further. -/
def isStructureDecl (env : Environment) (name : Name) : ConstantInfo → Bool
  | .inductInfo _ => Lean.isStructure env name
  | _ => false

/-- Test if `name` is an inductive definition. -/
def isInductiveDecl (env : Environment) (name : Name) : ConstantInfo → Bool
  | .inductInfo _ => !Lean.isStructure env name
  | _ => false

/-- Whether `name`'s declared type, once its arrow telescope is peeled off, is literally
`Decidable _`

Unlike `isCompilerGenerated`, this is purely syntactic so it can stay pure.

This mirrors the structure of `isErasableType` and its exception for `Decidable`.  Without this, a
hand-written decision procedure like `existsFileLocationVersion.decidable` (`Decidable (∃ loc, ..)`,
i.e. a `Comment → FileVersion → Decidable ..` telescope once uncurried) or an auto-derived
`DecidableEq` instance for one of `LgtmLean`'s types (`(a b : α) → Decidable (a = b)`) would be
swept up by `isCompilerGenerated`'s instance/name-shape heuristics below and never get a body. -/
partial def returnsDecidable (env : Environment) (name : Name) : Bool :=
  let rec peel : Expr → Expr
    | .forallE _ _ b _ => peel b
    | e => e
  match env.find? name with
  | some info =>
    match (peel info.type).getAppFn with
    | .const ``Decidable _ => true
    -- `DecidableEq`/`DecidablePred` are reducible abbreviations for a further `Decidable`-headed
    -- Pi type (`DecidableEq α := (a b : α) → Decidable (a = b)`), so an auto-`deriving DecidableEq`
    -- instance's *declared* type peels to one of these names.
    | .const ``DecidableEq _ => true
    | .const ``DecidablePred _ => true
    | _ => false
  | none => false

/-- Whether `name` is a declaration the compiler generated on our behalf (structure/inductive
machinery, equation lemmas, proof-irrelevant subterms, etc.) rather than something a person wrote.

This is the raw judgement, *without* `isCompilerGenerated`'s exemption for `Decidable`-returning
declarations; see `isDecidableExemption` for why the two are kept apart. -/
def isCompilerGeneratedCore (env : Environment) (name : Name) : Bool :=
  let hasBadLastComponent :=
    match name with
    | .str _ s =>
      s == "ctorIdx" || s == "ctorElimType" || s == "below" || s == "ibelow" || s == "ofNat" || s == "toCtorIdx" ||
        s.startsWith "_" || s.startsWith "eq_" || s.startsWith "match_" || s.startsWith "proof_" ||
        s.startsWith "omega_" || s.endsWith "_flat_ctor" || s.startsWith "sizeOf_spec" ||
        s.endsWith "noConfusionType" || s.startsWith "inst" || s.endsWith "decidable"
    | _ => true
  -- Catches instance-dictionary field projections (e.g. `instBEqFoo.beq`) and `match_N.splitter`
  -- helpers, whose last component looks ordinary but whose parent doesn't.
  let hasBadParentComponent :=
    match name.getPrefix with
    | .str _ s => s.startsWith "inst" || s.startsWith "match_"
    | _ => false
  Lean.isAuxRecursor env name || Lean.isNoConfusion env name || env.isProjectionFn name ||
    Lean.Meta.isInstanceCore env name || hasBadLastComponent || hasBadParentComponent

/-- `isCompilerGeneratedCore`, except that a `Decidable`-returning declaration is never treated as
compiler-generated. See `returnsDecidable` for why that exemption is needed and
`isDecidableExemption` for how its over-reach is undone. -/
def isCompilerGenerated (env : Environment) (name : Name) : Bool :=
  if returnsDecidable env name then
    false
  else
    isCompilerGeneratedCore env name

/-- Whether `name` survives `isCompilerGenerated` *only* because of its `returnsDecidable`
exemption, i.e. every other signal says the compiler wrote it.

`deriving DecidableEq` on a structure generates exactly such a pair (`instDecidableEqGitRevision`
and its `.decEq` worker), and the exemption is what stops the `startsWith "inst"` /
`isInstanceCore` checks from discarding them. That exemption has to be unconditional to be safe --
a `Decidable` value is real run-time data (see `isErasableType`), so a call site that branches on
one genuinely needs the definition -- but on its own it keeps *every* derived instance, reachable
or not.

The dictionary positions those instances occupy (`Std.HashMap`'s `[BEq]`/`[Hashable]`, `==`, ...)
are themselves erased and lowered to elisp `equal`, so in practice most of them end up referenced
by nothing but each other. `pruneToReachable` uses this predicate to seed a reachability pass with
everything else and drop the ones nothing actually calls. -/
def isDecidableExemption (env : Environment) (name : Name) : Bool :=
  returnsDecidable env name && isCompilerGeneratedCore env name


/-! ## Erasure -/

/-- Whether a value of type `ty` has no run-time representation.

Cases:

- `ty` is a `Prop` (so the value is a proof),
- `ty` is a `Sort` (so the value is a type, e.g. an implicit `{α : Type}` argument), or
- `ty` is a type class other than `Decidable` (so the value is a typeclass dictionary, e.g. `[BEq α]`/`[Hashable α]`).

 `Decidable` is deliberately excluded: elsewhere in the pipeline (`Decidable.decide`,
the `if`/`ite`/`cond` lifting of Prop-valued conditions to `Bool`) a `Decidable p` value is treated
as the actual computed answer, not a dispatch table, so erasing it would delete the very data those
call sites need. Every other class in this codebase (`BEq`, `Hashable`, `Min`, `Max`, `HAdd`, ...)
is used purely for dispatch -/
def isErasableType (ty : Expr) : Meta.MetaM Bool := do
  try
    if ← Meta.isProp ty then
      return true
    if let some className ← Meta.isClass? ty then
      if className != ``Decidable then
        return true
    return (← Meta.whnf ty).isSort
  catch _ =>
    return false

def isErasableValue (e : Expr) : Meta.MetaM Bool := do
  isErasableType (← Meta.inferType e)

def mkLApp (fn : LExpr) (args : List LExpr) : LExpr :=
  if args.isEmpty then fn else .app fn args

/-- Whether `n`'s last name component looks like an auto-generated matcher name (`match_1`,
`match_2`, ...). -/
def isLikelyMatcherName (n : Name) : Bool :=
  match n.eraseMacroScopes with
  | .str _ s => s.startsWith "match_"
  | _ => false

/-- A readable, Lisp-safe rendering of a binder's name.

Lean's match compiler, structure-update notation and pattern-matching lambdas name their binders
hygienically (`tail._@.LgtmLean.Threads.4103313803._hygCtx._hyg.47`). `toString` keeps those macro
scopes verbatim -- the `✝` seen in goal displays is added by the pretty-printer's name sanitizer,
not by `toString` -- so rendering them raw leaks unreadable identifiers into the elisp. Erasing the
scopes recovers the base name (`tail`).

Callers must pair this with `bindFresh`, which restores the distinctness the macro scopes were
providing: erasing scopes can collapse two genuinely different binders onto the same base. -/
def readableBinderName (n : Name) : String :=
  toString n.eraseMacroScopes

/-- Replace each `LPat.var` placeholder in `p` with the next entry pulled off `queue`, threading the
remaining queue through. A `none` entry becomes `LPat.wildcard` instead of a `var` so the result
doesn't invent a bogus binder name for something unused. -/
partial def relabelPat (p : LPat) (queue : List (Option String)) : LPat × List (Option String) :=
  match p with
  | .var _ =>
    match queue with
    | [] => (.wildcard, [])
    | n :: rest => ((match n with | some nm => .var nm | none => .wildcard), rest)
  | .ctor name fields =>
    let (fields', queue') := fields.foldl (fun (acc, q) f =>
      let (f', q') := relabelPat f q
      (acc ++ [f'], q')) ([], queue)
    (.ctor name fields', queue')
  | other => (other, queue)

def relabelPats (pats : List LPat) (queue : List (Option String)) :
    List LPat × List (Option String) :=
  pats.foldl (fun (acc, q) p =>
    let (p', q') := relabelPat p q
    (acc ++ [p'], q')) ([], queue)

/-! ## Translation of `Expr` into `LExpr` / `LPat`

Two independent mechanisms produce patterns, corresponding to the two ways Lean elaborates
pattern matching:

* A recursive (or otherwise multi-clause) top-level function is compiled via well-founded or
  structural recursion, which is very hard to decode faithfully from its raw `Expr` value. Instead
  `translateFunction` reads off Lean's auto-generated equation lemmas (`f.eq_1`, `f.eq_2`, ...),
  whose statement `∀ xs, f pat₁ ... patₙ = rhs` already exposes exactly the patterns and right-hand
  sides written at the definition site (see `exprToPat`).
* A `match ... with` expression occurring inside a body (whether that body came from an
  equation's right-hand side or from an ordinary non-recursive function) is compiled into a call
  to a separate auxiliary "matcher" definition, whose own value is a tree of `casesOn`
  applications. `tryDecodeMatcher` walks that tree once per call site to recover the patterns.
-/

open Meta in
/-- Translate the left-hand-side argument `e` of an equation lemma into a pattern. Such arguments
are always already in constructor-normal form (variables, literals, or a constructor applied to
more of the same), by construction of the equation compiler. -/
partial def exprToPat (varNames : Std.HashMap FVarId String) (e : Expr) : MetaM LPat := do
  match e with
  | .mdata _ b => exprToPat varNames b
  | .fvar fvid => pure ((varNames[fvid]?.map LPat.var).getD .wildcard)
  | .lit (.natVal n) => pure (.lit (.nat n))
  | .lit (.strVal s) => pure (.lit (.str s))
  | .app (.const ``Char.ofNat _) (.lit (.natVal n)) => pure (.lit (.char (Char.ofNat n)))
  | _ =>
    e.withApp fun fn args => do
      match fn with
      | .const cName _ =>
        if cName == ``OfNat.ofNat && args.size ≥ 2 then
          match args[1]! with
          | .lit (.natVal n) => return .lit (.nat n)
          | _ => ctorPat varNames cName args
        else
          ctorPat varNames cName args
      | _ => pure .wildcard
where
  ctorPat (varNames : Std.HashMap FVarId String) (cName : Name) (args : Array Expr) : MetaM LPat := do
    match (← getEnv).find? cName with
    | some (.ctorInfo _) => do
      let mut fields : List LPat := []
      for a in args do
        if ← isErasableValue a then
          pure ()
        else
          fields := fields ++ [← exprToPat varNames a]
      pure (.ctor (toString cName) fields)
    | _ => pure .wildcard

/-- Whether `n` was invented by the elaborator rather than written by the user. This happens when a
function parameter is bound via a pattern instead of a plain name (e.g. `def f : Nat → Nat | 0 =>
.. | n+1 => ..`).

`translateFunction` uses this to reject that pattern-bound function definition form, which
`LFunction`'s flat `parameters : List String` cannot represent. It also happens, harmlessly, for an
anonymous instance-implicit binder (e.g. `[BEq α]`), but `translateFunction` never checks this
function against those. `isErasableType` erases every instance-implicit parameter before its name
would ever be examined. -/
def isElaboratorGeneratedName (n : Name) : Bool :=
  n.hasMacroScopes

/-- A stable, Lisp-safe name for a parameter binder. Falls back to a synthetic name when the
binder's own name was invented by the elaborator (see `isElaboratorGeneratedName`).  That
happens for eta-expansion's synthesized trailing parameters (see `translateApp`), since those
don't come from a real source-level binder. -/
def paramNameOrFallback (n : Name) (idx : Nat) : String :=
  if isElaboratorGeneratedName n then s!"etaArg{idx}" else toString n

/-- Extend `varNames` with `fvarId ↦ candidate`, appending `fvarId`'s own unique internal id to
`candidate` first if that name is already bound to some *other* fvar still in scope.

Lean's own binder names aren't required to be distinct across nested scopes, as the
compiler resolves references using `FVarId`s instead of names.  Many generated terms
use generic variable names that end up shadowing each other. -/
def bindFresh (varNames : Std.HashMap FVarId String) (fvarId : FVarId) (candidate : String) :
    Std.HashMap FVarId String × String :=
  let nm :=
    if varNames.toList.any (fun (fv, n) => fv != fvarId && n == candidate) then
      candidate ++ "-" ++ toString (hash fvarId.name)
    else
      candidate
  (varNames.insert fvarId nm, nm)

mutual

partial def translateConstRef (n : Name) : Meta.MetaM LExpr := do
  match (← getEnv).find? n with
  | some (.ctorInfo _) => pure (.ctorRef (toString n))
  | _ =>
    if n == ``sorryAx then pure (.opaque "sorry") else pure (.global (toString n))

/-- Translate an arbitrary term. `varNames` maps every locally-bound `FVarId` currently in scope
(from an enclosing `lam`/`letE`/pattern) to the name it should be rendered under. -/
partial def translateExpr (varNames : Std.HashMap FVarId String) (e : Expr) : Meta.MetaM LExpr := do
  match e with
  | .mdata _ b => translateExpr varNames b
  | .lit (.natVal n) => pure (.lit (.nat n))
  | .lit (.strVal s) => pure (.lit (.str s))
  | .fvar fvid =>
    match varNames[fvid]? with
    | some n => pure (.var n)
    | none => pure (.opaque s!"reference to an erased/unbound local variable")
  | .proj structName idx target => do
    let fields := getStructureFields (← getEnv) structName
    let fieldName := if h : idx < fields.size then toString fields[idx] else s!"field{idx}"
    let targetL ← translateExpr varNames target
    pure (.proj (toString structName) fieldName targetL)
  | .letE n ty v b _ => do
    let erase ← isErasableType ty
    Meta.withLetDecl n ty v fun fvar => do
      let (varNames', nm) := bindFresh varNames fvar.fvarId! (readableBinderName n)
      let bL ← translateExpr varNames' (b.instantiate1 fvar)
      if erase then
        pure bL
      else
        let vL ← translateExpr varNames v
        pure (.letE nm vL bL)
  | .lam .. =>
    Meta.lambdaTelescope e fun xs body => do
      let mut varNames' := varNames
      let mut paramNames : List String := []
      for x in xs do
        let ld ← x.fvarId!.getDecl
        let (vn, nm) := bindFresh varNames' x.fvarId! (readableBinderName ld.userName)
        varNames' := vn
        if !(← isErasableType ld.type) then
          paramNames := paramNames ++ [nm]
      let bodyL ← translateExpr varNames' body
      pure (.lam paramNames bodyL)
  | .app .. => translateApp varNames e
  | .const n _ => translateConstRef n
  | _ => pure (.opaque s!"unsupported term shape")

/-- Translate a (possibly under-saturated) application.

If `e`'s type is still a function type (e.g., due to currying) eta-expand it into an explicit `LExpr.lam` over the remaining parameters before
translating, since Lisp targets don't support Lean's implicit currying.

Otherwise, checks whether the head looks like an auto-generated matcher and, if so, tries to decode
it into `LExpr.matchE`.

Otherwise (or if decoding fails) falls back to translating it as an ordinary call, erasing
`Prop`/`Sort` arguments and special-casing the `cond`/`ite` primitives into `LExpr.ite`. -/
partial def translateApp (varNames : Std.HashMap FVarId String) (e : Expr) : Meta.MetaM LExpr := do
  let eType ← Meta.whnf (← Meta.inferType e)
  if eType.isForall then
    Meta.forallTelescope eType fun tailXs _ => do
      let mut varNames' := varNames
      let mut tailNames : List String := []
      for x in tailXs do
        let ld ← x.fvarId!.getDecl
        unless ← isErasableType ld.type do
          let (vn, nm) := bindFresh varNames' x.fvarId! (paramNameOrFallback ld.userName tailNames.length)
          varNames' := vn
          tailNames := tailNames ++ [nm]
      let bodyL ← translateApp varNames' (mkAppN e tailXs)
      pure (.lam tailNames bodyL)
  else
    e.withApp fun fn args => do
      -- `if h : c then t else e` (as opposed to the non-dependent `if c then t else e`) elaborates
      -- to `dite (α := _) c inst t e`, where `t : c → α` and `e : ¬c → α` are functions of the
      -- (erased) decidability proof rather than plain values of `α`. This is in contrast to
      -- `ite`/`cond`, whose branches already are `α`-valued and so fall out of the generic
      -- `keptArgs` handling below as an `.ite` once `c`/`α` erase away.
      --
      -- Translating `dite` the same generic way would leave its two branches as zero-argument
      -- thunks (since the proof parameter erases) passed to a `dite`/`lgtm-dite`
      -- call.
      let isDite := match fn with
        | .const ``dite _ => args.size == 5
        | _ => false
      if isDite then
        let instL ← translateExpr varNames args[2]!
        let thenL ← Meta.lambdaTelescope args[3]! fun _ body => translateExpr varNames body
        let elseL ← Meta.lambdaTelescope args[4]! fun _ body => translateExpr varNames body
        return .ite instL thenL elseL
      let matcherResult? ← match fn with
        | .const cName _ =>
          if isLikelyMatcherName cName then tryDecodeMatcher varNames cName args else pure none
        | _ => pure none
      match matcherResult? with
      | some r => pure r
      | none => do
        -- A field of function type can appear applied to more arguments than just the structure
        -- instance. Lean's currying makes this indistinguishable from an ordinary
        -- function application in a way that renders incorrectly in elisp.
        --
        -- Example: `Configuration.createComment` compiles to a `cl-defstruct` accessor of arity
        -- exactly one. Splitting off the field access from the extra arguments (which get funcall'd
        -- onto the result, see `LExpr.toSExpr`'s `.proj` case in `Render.lean`) keeps that arity
        -- correct. Class-method projections (`BEq.beq` and friends) are excluded since those are
        -- already special-cased whole in `translatePrimitives`, which expects them pre-flattened.
        let projResult? ← match fn with
          | .const cName _ => do
            match ← getProjectionFnInfo? cName with
            | some info =>
              -- Restricted to structures we actually emit a `cl-defstruct` for: `Prod.fst` is a
              -- projection too, but it is translated whole by `translatePrimitives` (to an `elt`
              -- call), and rewriting it to a `.proj` here would name an accessor that is never
              -- defined.
              let structName := info.ctorName.getPrefix
              if !info.fromClass && isLgtmLeanDecl (← getEnv) structName && info.numParams < args.size then
                let projL ← translateExpr varNames (.proj structName info.i args[info.numParams]!)
                let mut keptExtra : List LExpr := []
                for a in args.extract (info.numParams + 1) args.size do
                  if ← isErasableValue a then
                    pure ()
                  else
                    keptExtra := keptExtra ++ [← translateExpr varNames a]
                pure (some (mkLApp projL keptExtra))
              else
                pure none
            | none => pure none
          | _ => pure none
        match projResult? with
        | some r => pure r
        | none => do
          let fnL ← translateExpr varNames fn
          -- A constructor application starts with the inductive's parameters, which are not
          -- fields: nothing of them survives into the constructed value, so the `cl-defstruct`
          -- constructor (or tagged vector) takes only the arguments after them. They usually erase
          -- anyway, being types; a structure parameterized by *data* (`FileThreadsBootstrapState`,
          -- indexed by the two maps its invariants talk about) is what makes this explicit.
          let ctorParams ← match fn with
            | .const cName _ => do
              match (← getEnv).find? cName with
              | some (.ctorInfo ctorInfo) => pure ctorInfo.numParams
              | _ => pure 0
            | _ => pure 0
          let mut keptArgs : List LExpr := []
          for a in args.extract ctorParams args.size do
            if ← isErasableValue a then
              pure ()
            else
              keptArgs := keptArgs ++ [← translateExpr varNames a]
          match fn, keptArgs with
          | .const cName _, [c, t, eBr] =>
            if cName == ``cond || cName == ``ite then pure (.ite c t eBr) else pure (mkLApp fnL keptArgs)
          | _, _ => pure (mkLApp fnL keptArgs)

/-- Overwrite the node at `path` (a chain of `ctor`-field indices, root-to-leaf) within `pat` with
`sub`. Each row only ever inserts a shallower entry before any of its deeper extensions (see
`decomposeCasesOn`, which prepends its own `(rootPos, path, ..)` in front of everything its
recursive call already produced), so every prefix of `path` is already a `ctor` node by the time
it's reached; `pat` is returned unchanged if that invariant is somehow violated. -/
partial def insertAtPath (pat : LPat) (path : List Nat) (sub : LPat) : LPat :=
  match path with
  | [] => sub
  | i :: rest =>
    match pat with
    | .ctor name fields => .ctor name (fields.set i (insertAtPath (fields.getD i .wildcard) rest sub))
    | _ => pat

/-- Try to decode a call `matcherName args...` into an `LExpr.matchE`.

`matcherName`'s uninstantiated value has the shape `fun params motive discrs alts => <tree of
casesOn on the discrs>`, with the tree's leaves being bare applications of one of the `alts`
binders. We walk that tree once (`walkMatcherBody`) to recover, per leaf, which discriminants were
scrutinized to reach it. The real per-alternative bodies (with real bound-variable names) are then
read off of `args` at the corresponding position, not out of the generic tree. Returns `none`
(falling back to ordinary call translation) if `matcherName` isn't actually a matcher-shaped
definition, e.g. because it doesn't delta-reduce to a recognizable `casesOn` tree at all.

A discriminant position whose type is erasable (e.g. a `Prop` destructured purely to unpack proof
obligations, as in `let ⟨hFound, ...⟩ := hAll entry mem⟩`) is dropped from the emitted pattern
rather than rendered as a `pcase` branch. -/
partial def tryDecodeMatcher (varNames : Std.HashMap FVarId String) (matcherName : Name) (args : Array Expr) :
    Meta.MetaM (Option LExpr) := do
  let some ci := (← getEnv).find? matcherName | return none
  let some matcherVal := ci.value? | return none
  Meta.lambdaTelescope matcherVal fun xs body => do
    if xs.size != args.size then return none
    let mut topPos : Std.HashMap FVarId Nat := {}
    let mut varPos : Std.HashMap FVarId (Nat × List Nat) := {}
    for i in [0:xs.size] do
      topPos := topPos.insert xs[i]!.fvarId! i
      varPos := varPos.insert xs[i]!.fvarId! (i, [])
    let rows ← walkMatcherBody topPos varPos body
    if rows.isEmpty then return none
    let allPositions := ((rows.flatMap (fun (assoc, _) => assoc.map (·.1))).eraseDups).mergeSort (· ≤ ·)
    if allPositions.isEmpty then return none
    let mut keptPositions : List Nat := []
    for p in allPositions do
      unless ← isErasableValue args[p]! do
        keptPositions := keptPositions ++ [p]
    if keptPositions.isEmpty then
      -- Every discriminant is erasable, so there is exactly one reachable row -- translate its body
      -- directly instead of emitting a meaningless `pcase` over dead, proof-irrelevant data.
      let (_, altFv) := rows.head!
      let some altPos := topPos[altFv]? | return none
      Meta.lambdaTelescope args[altPos]! fun realXs realBody => do
        let mut varNames' := varNames
        for rx in realXs do
          let ld ← rx.fvarId!.getDecl
          let (vn, _) := bindFresh varNames' rx.fvarId! (readableBinderName ld.userName)
          varNames' := vn
        some <$> translateExpr varNames' realBody
    else
      let discrExprs ← keptPositions.mapM (fun p => translateExpr varNames args[p]!)
      let mut alts : List (List LPat × LExpr) := []
      for (assoc, altFv) in rows do
        let some altPos := topPos[altFv]? | continue
        let altArgExpr := args[altPos]!
        let clause ← Meta.lambdaTelescope altArgExpr fun realXs realBody => do
          let mut varNames' := varNames
          -- A binder the alternative's body never mentions becomes a `_` pattern rather than an
          -- invented name. This is what the user wrote as `_` in the source: the match compiler has
          -- to bind *something* there, so it invents a hygienic name, but nothing can refer to it.
          let mut nameStrs : List (Option String) := []
          for rx in realXs do
            let ld ← rx.fvarId!.getDecl
            let (vn, nm) := bindFresh varNames' rx.fvarId! (readableBinderName ld.userName)
            varNames' := vn
            nameStrs := nameStrs ++ [if realBody.containsFVar rx.fvarId! then some nm else none]
          let bodyL ← translateExpr varNames' realBody
          -- Several entries in `assoc` can share the same root position `p` so fold them into `p`'s
          -- pattern shallowest-first, inserting each deeper `ctor` into the placeholder its
          -- immediate parent already reserved.  Relabeling walks every position (not just the
          -- kept ones) in the same order the names were bound in, so the queue stays aligned; only
          -- afterwards do we drop the erased positions' (now-irrelevant) patterns from what's
          -- actually emitted.
          let rawPats := allPositions.map (fun p =>
            let entries := (assoc.filter (·.1 == p)).map (fun (_, path, pat) => (path, pat))
            let sorted := entries.mergeSort (fun a b => a.1.length ≤ b.1.length)
            sorted.foldl (fun acc (path, pat) => insertAtPath acc path pat) (.var "_"))
          let (labeledPats, _) := relabelPats rawPats nameStrs
          let keptPats := (allPositions.zip labeledPats).filterMap
            (fun (p, pat) => if keptPositions.contains p then some pat else none)
          pure (keptPats, bodyL)
        alts := alts ++ [clause]
      return some (.matchE discrExprs alts)

/-- Walk a matcher's generic `casesOn` tree. Returns one row per leaf reached: the assoc-list
of (root discriminant position, path of ctor-field indices from that root, constructor pattern at
that path) accumulated on the way there, plus the `FVarId` (one of `topPos`'s keys) of the
alternative binder applied at that leaf. A discriminant (or field of one) that's never destructured
on some path (e.g. a wildcard `_` pattern) doesn't appear in that row's assoc-list.
`tryDecodeMatcher` pads for this using the union of root positions seen across all rows, and
defaults any un-visited field within a visited root to a plain variable.

A named/dependent match (`match h : e with`) makes the matcher's motive depend on the scrutinee
equality, so the elaborator wraps the real `casesOn` tree in an extra redex to thread that equality proof through.
Example: `(fun x_1 => casesOn ... x_1 ...) x (Eq.refl x)`

`headBeta` strips exactly that wrapper (without unfolding any definitions, unlike `whnf`) so the
`casesOn` node underneath is still recognized. It's a no-op everywhere else. -/
partial def walkMatcherBody (topPos : Std.HashMap FVarId Nat) (varPos : Std.HashMap FVarId (Nat × List Nat))
    (e : Expr) : Meta.MetaM (List (List (Nat × List Nat × LPat) × FVarId)) := do
  match e.headBeta.getAppFn with
  | .const casesOnName _ =>
    let indName := casesOnName.getPrefix
    if casesOnName == indName ++ `casesOn then
      decomposeCasesOn topPos varPos indName e.headBeta
    else if casesOnName == ``dite then
      decomposeDiteLiteral topPos varPos e.headBeta
    else
      pure []
  | .fvar fvid => pure (if topPos.contains fvid then [([], fvid)] else [])
  | _ => pure []

/-- Decompose one `indName.casesOn params motive major minor₁ ... minorₖ` node (`k` = number of
constructors of `indName`, in declaration order) and recurse into each `minorᵢ`, which is a
function of that constructor's fields. Only handles non-indexed inductives (true of every type
`LgtmLean` actually pattern-matches on: `Bool`, `List`, `Option`, `Nat`, and its own plain enums).

`major` need not be one of the matcher's own top-level discriminants directly (`varPos[·]` covers
both cases uniformly via an empty vs. non-empty path): it may instead be a field variable this same
function bound while decomposing an *enclosing* `casesOn`, which is what makes a source pattern like
`((.topLevel, _), _)` decodable, since Lean compiles it into one matcher whose body chains `casesOn`
nodes directly rather than delegating the inner level to its own auxiliary matcher. -/
partial def decomposeCasesOn (topPos : Std.HashMap FVarId Nat) (varPos : Std.HashMap FVarId (Nat × List Nat))
    (indName : Name) (e : Expr) : Meta.MetaM (List (List (Nat × List Nat × LPat) × FVarId)) := do
  match (← getEnv).find? indName with
  | some (.inductInfo indInfo) => do
    let args := e.getAppArgs
    let base := indInfo.numParams + 1 + 1
    if args.size < base + indInfo.ctors.length then return []
    match args[indInfo.numParams + 1]! with
    | .fvar fvid =>
      match varPos[fvid]? with
      | none => pure []
      | some (rootPos, path) => do
        let mut allRows : List (List (Nat × List Nat × LPat) × FVarId) := []
        for i in [0:indInfo.ctors.length] do
          let ctorName := indInfo.ctors[i]!
          let minor := args[base + i]!
          let rows ← Meta.lambdaTelescope minor fun fieldVars minorBody => do
            let placeholders := fieldVars.toList.map (fun _ => LPat.var "_")
            let mut varPos' := varPos
            for j in [0:fieldVars.size] do
              varPos' := varPos'.insert fieldVars[j]!.fvarId! (rootPos, path ++ [j])
            let subRows ← walkMatcherBody topPos varPos' minorBody
            pure (subRows.map (fun (assoc, altFv) =>
              ((rootPos, path, LPat.ctor (toString ctorName) placeholders) :: assoc, altFv)))
          allRows := allRows ++ rows
        pure allRows
    | _ => pure []
  | _ => pure []

/-- Decompose one `dite (scrutinee = lit) inst thenBranch elseBranch` node.

This is how Lean compiles a `match` against a literal value (`Nat`, `String`, or `Char.ofNat n`).
The `Char` form is odd because `Char` has no constructors of its own.

`thenBranch`'s value is `@Eq.ndrec_symm α lit motive (h Unit.unit) scrutinee`: since
`Eq.ndrec_symm`'s signature is `.. → motive a → {b} → b = a → motive b`, this partial application (5
of its 6 explicit args) already has the function type `dite` needs for its `t : cond → α` argument,
with no further eta-expansion. -/
partial def decomposeDiteLiteral (topPos : Std.HashMap FVarId Nat) (varPos : Std.HashMap FVarId (Nat × List Nat))
    (e : Expr) : Meta.MetaM (List (List (Nat × List Nat × LPat) × FVarId)) := do
  let args := e.getAppArgs
  if args.size < 5 then return []
  let condProp := args[1]!
  let thenBranch := args[3]!
  let elseBranch := args[4]!
  match condProp.getAppFn, condProp.getAppArgs with
  | .const ``Eq _, eqArgs =>
    if eqArgs.size != 3 then return []
    match eqArgs[1]! with
    | .fvar fvid =>
      match varPos[fvid]? with
      | none => pure []
      | some (rootPos, path) =>
        let litPat? : Option LPat := match eqArgs[2]! with
          | .lit (.natVal n) => some (.lit (.nat n))
          | .lit (.strVal s) => some (.lit (.str s))
          | .app (.const ``Char.ofNat _) (.lit (.natVal n)) => some (.lit (.char (Char.ofNat n)))
          | _ => none
        match litPat? with
        | none => pure []
        | some litPat => do
          let thenAlts : List FVarId := match thenBranch.getAppFn with
            | .const ``Eq.ndrec_symm _ =>
              let ndrecArgs := thenBranch.getAppArgs
              if ndrecArgs.size < 4 then [] else
                match ndrecArgs[3]!.headBeta.getAppFn with
                | .fvar altFv => if topPos.contains altFv then [altFv] else []
                | _ => []
            | _ => []
          let elseRows ← Meta.lambdaTelescope elseBranch fun _ elseBody => walkMatcherBody topPos varPos elseBody
          pure (thenAlts.map (fun altFv => ([(rootPos, path, litPat)], altFv)) ++ elseRows)
    | _ => pure []
  | _, _ => pure []

end

/-- Whether equation clause `pats` is just the trivial variable patterns naming `params`, in
order. That is, if the clause doesn't actually destructure any of its arguments. When it's the sole
clause, `translateFunction` uses its body directly instead of wrapping it in a redundant
single-alternative `LExpr.matchE`. -/
def isTrivialClause (pats : List LPat) (params : List String) : Bool :=
  pats.length == params.length && (pats.zip params).all fun (p, n) =>
    match p with
    | .var m => m == n
    | _ => false

/-- Translate a single top-level `LgtmLean` function into its `LFunction` representation.

Reads the function's parameter names directly off its declared type, throwing if any non-erasable
parameter's name was invented by the elaborator rather than written by the user.  That only happens
for the pattern-bound function definition forms, so extractable code should avoid that definition
style.

The body then prefers Lean's auto-generated equation lemmas, which is what lets recursive functions
come through as ordinary pattern matching instead of the raw well-founded/structural recursion
combinators they actually compile to.  Falls back to directly reading off `lambdaTelescope` of
the definition's value for functions with no equations (e.g. a one-line non-recursive `def` with no
internal `match`). Multiple equation clauses (or a single clause that does destructure its
arguments, e.g. a single-constructor structure) are recombined into one `LExpr.matchE` over the
declared parameters. -/
def translateFunction (name : Name) : Meta.MetaM LFunction := do
  let info ← getConstInfo name
  let docstring ← findDocString? (← getEnv) name
  let isPublic := isPublicApi (← getEnv) name
  let eqns? ← Meta.getEqnsFor? name
  -- When equations exist, the real per-clause patterns are read off separately below (via
  -- `exprToPat`, from each equation lemma's LHS), so this telescope's names only need to be some
  -- stable, distinct, Lisp-safe identifiers to serve as `LFunction.parameters`/the top-level
  -- `matchE` scrutinee list, a synthetic fallback name is safe here rather than a hard
  -- failure. This is what lets a compiler-`deriving`-generated instance like
  -- `instDecidableEqCommentRef.decEq`.
  let paramNames ← Meta.forallTelescope info.type fun xs _ => do
    let mut names : List String := []
    for x in xs do
      let ld ← x.fvarId!.getDecl
      unless ← isErasableType ld.type do
        if isElaboratorGeneratedName ld.userName then
          if eqns?.isSome then
            names := names ++ [paramNameOrFallback ld.userName names.length]
          else
            throwError s!"{name} binds a parameter via a pattern instead of a name"
        else
          names := names ++ [toString ld.userName]
    pure names
  match eqns? with
  | some eqns => do
    let mut clauses : List (List LPat × LExpr) := []
    for eqnName in eqns do
      let eqnInfo ← getConstInfo eqnName
      let clause ← Meta.forallTelescope eqnInfo.type fun xs eqType => do
        let mut varNames : Std.HashMap FVarId String := {}
        for x in xs do
          let ld ← x.fvarId!.getDecl
          let (vn, _) := bindFresh varNames x.fvarId! (readableBinderName ld.userName)
          varNames := vn
        match eqType.eq? with
        | none => pure ([LPat.wildcard], LExpr.opaque "malformed equation lemma")
        | some (_, lhs, rhs) => do
          let mut pats : List LPat := []
          for a in lhs.getAppArgs do
            if ← isErasableValue a then
              pure ()
            else
              pats := pats ++ [← exprToPat varNames a]
          let bodyL ← translateExpr varNames rhs
          pure (pats, bodyL)
      clauses := clauses ++ [clause]
    -- `paramNames` (from `info.type`'s telescope) can come back shorter than the equations' arity.
    -- This seems to happen around `DecidableEq` instances.  The extra names are purely cosmetic
    -- scrutinee bindings for the `matchE` below so falling back to a synthetic name per clause
    -- parameter is safe whenever the arities disagree.
    let arity := (clauses.headD ([], LExpr.opaque "")).1.length
    let paramNames := if paramNames.length == arity then paramNames else
      (List.range arity).map (s!"arg{·}")
    let body := match clauses with
      | [(pats, bodyL)] =>
        if isTrivialClause pats paramNames then bodyL else .matchE (paramNames.map LExpr.var) clauses
      | _ => .matchE (paramNames.map LExpr.var) clauses
    pure { name := toString name, parameters := paramNames, body, docstring, isPublic }
  | none =>
    match info.value? with
    | none =>
      let body := LExpr.opaque "no definition available"
      pure { name := toString name, parameters := paramNames, body, docstring, isPublic }
    | some v =>
      Meta.lambdaTelescope v fun xs body => do
        let mut varNames : Std.HashMap FVarId String := {}
        for x in xs do
          let ld ← x.fvarId!.getDecl
          varNames := varNames.insert x.fvarId! (toString ld.userName)
        let bodyL ← translateExpr varNames body
        pure { name := toString name, parameters := paramNames, body := bodyL, docstring, isPublic }

-- Regression test: `LgtmLean.Files.parseFileModificationType` matches its `Char` parameter against
-- literal patterns (`'M'`, `'A'`, ...). Since it's non-recursive, `translateFunction` takes this
-- function's equation-lemma path, converting each equation's left-hand-side argument via
-- `exprToPat`.
/-- info: "LPat.lit (LLit.char 'M'), LPat.lit (LLit.char 'A'), LPat.lit (LLit.char 'D'), LPat.lit (LLit.char 'T'), LPat.lit (LLit.char 'R'), LPat.lit (LLit.char 'C'), LPat.var \"c\"" -/
#guard_msgs in
#eval show Meta.MetaM String from do
  let f ← translateFunction `parseFileModificationType
  match f.body with
  | .matchE _ alts => pure (", ".intercalate (alts.map (fun (pats, _) => reprStr pats.head!)))
  | _ => pure "no matchE"

/-- Whether `name`'s declared type has no run-time representation once its full arrow
telescope is peeled off: either a `Prop` (a proof-producing predicate like
`SelectedComment.WellFormed`) or a `Sort` (a type synonym like `abbrev CommentThread := ...`).
Neither is really a "function" in the run-time sense.  Translating its body would just erase
everything down to a meaningless husk, so `main` skips these outright rather than emitting one. -/
def isPropReturningDecl (name : Name) : Meta.MetaM Bool := do
  try
    Meta.forallTelescope (← getConstInfo name).type fun _ codomain => isErasableType codomain
  catch _ =>
    return false

/-- Whether the inductive `name` is a `Prop` or `Sort.

Checks `codomain.isProp` (is this expression *literally* the sort `Prop`), not `Meta.isProp
codomain` (is the *type of* this expression `Prop`, which asks a different question here since
`codomain` is itself a classifying sort, not a value). Also deliberately does not treat a
`Type`-valued codomain as erasable the way `isPropReturningDecl` does for functions: every ordinary
data inductive's declared type is itself `Type`-sorted so that check would reject every inductive,
not just the proof-only ones. -/
def isPropSortedInductive (name : Name) : Meta.MetaM Bool := do
  try
    Meta.forallTelescope (← getConstInfo name).type fun _ codomain => do
      pure (← Meta.whnf codomain).isProp
  catch _ =>
    return false

/-- Translate a single top-level `LgtmLean` structure into its `LStructureDefinition`
representation. Discards any fields of erasable types (e.g., Prop). -/
def translateStructure (name : Name) : Meta.MetaM LStructureDefinition := do
  let env ← getEnv
  let ctor := Lean.getStructureCtor env name
  Meta.forallTelescope ctor.type fun xs _ => do
    let mut fields : List String := []
    -- The constructor's leading `numParams` binders are the structure's *parameters*, not its
    -- fields.  E.g., `FileThreadsBootstrapState origState comments₁` is a family of types indexed
    -- by two values. They only exist to pin down the type, so they have no slot in the
    -- `cl-defstruct`. `translateApp` drops them from projection applications to match.
    for x in xs.extract ctor.numParams xs.size do
      let ld ← x.fvarId!.getDecl
      unless ← isErasableType ld.type do
        fields := fields ++ [toString ld.userName]
    pure { name := toString name, fields, isPublic := isPublicApi env name }

/-- Translate a single top-level `LgtmLean` (non-structure) inductive into its
`LInductiveDefinition` representation: one `(name, arity)` pair per constructor, where the arity
discards any constructor field of an erasable type (e.g., Prop). -/
def translateInductive (name : Name) : Meta.MetaM LInductiveDefinition := do
  match ← getConstInfo name with
  | .inductInfo indInfo => do
    let mut ctors : List (String × Nat) := []
    for ctorName in indInfo.ctors do
      let ctorInfo ← getConstInfo ctorName
      let arity ← Meta.forallTelescope ctorInfo.type fun xs _ => do
        let mut n := 0
        for x in xs do
          let ld ← x.fvarId!.getDecl
          unless ← isErasableType ld.type do
            n := n + 1
        pure n
      ctors := ctors ++ [(toString ctorName, arity)]
    pure { name := toString name, constructors := ctors }
  | _ => throwError s!"{name} is not an inductive definition"

def getFunctionNames (env : Environment) : List Name :=
  let names := env.constants.toList.filterMap fun (name, info) =>
    if isFunctionDecl info && isLgtmLeanDecl env name && !isCompilerGenerated env name then
      some name
    else
      none
  names.mergeSort (·.toString ≤ ·.toString)

def getStructureNames (env : Environment) : List Name :=
  let names := env.constants.toList.filterMap fun (name, info) =>
    if isStructureDecl env name info && isLgtmLeanDecl env name && !isCompilerGenerated env name then
      some name
    else
      none
  names.mergeSort (·.toString ≤ ·.toString)

def getInductiveNames (env : Environment) : List Name :=
  let names := env.constants.toList.filterMap fun (name, info) =>
    if isInductiveDecl env name info && isLgtmLeanDecl env name && !isCompilerGenerated env name then
      some name
    else
      none
  names.mergeSort (·.toString ≤ ·.toString)

/-- The names in `funcMap` reachable from `roots` by following `LExpr.global` references.

Names in `roots` are always reachable, including ones with no `funcMap` entry (a declaration whose
translation failed), which simply contribute no further edges. -/
partial def reachableFunctions (funcMap : Std.HashMap String LFunction) (roots : List String) :
    Std.HashSet String :=
  go Std.HashSet.emptyWithCapacity roots
where
  go (seen : Std.HashSet String) : List String → Std.HashSet String
    | [] => seen
    | name :: rest =>
      if seen.contains name then
        go seen rest
      else
        let seen := seen.insert name
        match funcMap[name]? with
        | none => go seen rest
        | some f => go seen (f.body.globalRefs ++ rest)

section ReachabilityTests

private def testFn (name : String) (body : LExpr) : LFunction :=
  { name := name, parameters := [], body := body, docstring := none }

/-- `root` calls `used`, which calls `alsoUsed`; `dead` is referenced by nothing, and `List.map`
is a reference with no `funcMap` entry of its own. -/
private def testFuncMap : Std.HashMap String LFunction :=
  Std.HashMap.ofList
    [ ("root", testFn "root" (.app (.global "List.map") [.global "used"])),
      ("used", testFn "used" (.matchE [.var "x"] [([.wildcard], .global "alsoUsed")])),
      ("alsoUsed", testFn "alsoUsed" (.lit (.nat 0))),
      -- A cycle among the unreachable definitions, which must not diverge.
      ("dead", testFn "dead" (.ite (.global "alsoDead") (.global "dead") (.lit (.nat 1)))),
      ("alsoDead", testFn "alsoDead" (.global "dead")) ]

/-- info: ["List.map", "alsoUsed", "root", "used"] -/
#guard_msgs in
#eval (reachableFunctions testFuncMap ["root"]).toList.mergeSort (· ≤ ·)

-- A root that reaches nothing, and a root that isn't in the map at all, are both still kept.
/-- info: ["alsoUsed", "untranslatable"] -/
#guard_msgs in
#eval (reachableFunctions testFuncMap ["alsoUsed", "untranslatable"]).toList.mergeSort (· ≤ ·)

end ReachabilityTests

/-- Drop the translated functions that nothing else refers to.

Every function is its own root except the `isDecidableExemption` ones, so this only ever removes
auto-derived `Decidable` machinery -- an exported helper that happens to have no caller inside the
extracted set is still emitted, since hand-written elisp may well call it.

`names` supplies the original `Name`s because `funcMap` is keyed by `toString`, which doesn't
round-trip through `String.toName` for the mangled module-private names (`_private.LgtmLean.
Interface.0.foo` has a *numeric* `0` component). -/
def pruneToReachable (env : Environment) (names : List Name)
    (funcMap : Std.HashMap String LFunction) : Std.HashMap String LFunction :=
  let roots := names.filterMap fun name =>
    if isDecidableExemption env name then none else some name.toString
  let reachable := reachableFunctions funcMap roots
  funcMap.filter fun name _ => reachable.contains name

def translateLeanDefinitions (env : Environment) : MetaM (Translations String) := do
  -- FIXME: just put these into MetaM and incorporate isPropSortedInductive and isPropReturningDecl
  -- to avoid redundant validation
  let functionNames := getFunctionNames env
  let structureNames := getStructureNames env
  let inductiveNames := getInductiveNames env

  let mut funcMap : Std.HashMap String LFunction := Std.HashMap.emptyWithCapacity
  for name in functionNames do
    unless ← isPropReturningDecl name do
      try
        let f ← translateFunction name
        funcMap := funcMap.insert name.toString f
      catch ex =>
        IO.eprintln s!"-- failed to translate {name}: {(← ex.toMessageData.format).pretty}"
  funcMap := pruneToReachable env functionNames funcMap

  let mut structMap : Std.HashMap String LStructureDefinition := Std.HashMap.emptyWithCapacity
  for name in structureNames do
    try
      let s ← translateStructure name
      structMap := structMap.insert name.toString s
    catch ex =>
      IO.eprintln s!"-- failed to translate {name}: {(← ex.toMessageData.format).pretty}"

  let mut inductiveMap : Std.HashMap String LInductiveDefinition := Std.HashMap.emptyWithCapacity
  for name in inductiveNames do
    unless ← isPropSortedInductive name do
      try
        let i ← translateInductive name
        inductiveMap := inductiveMap.insert name.toString i
      catch ex =>
        IO.eprintln s!"-- failed to translate {name}: {(← ex.toMessageData.format).pretty}"

  pure ⟨funcMap, structMap, inductiveMap⟩


def runMeta (env : Environment) (action : MetaM α) : IO α := do
  let coreCtx : Core.Context := { fileName := "extractor", fileMap := default }
  let coreState₀ : Core.State := { env := env }
  let ((res, _savedState), _coreState₁) ← (action.run {} {}).toIO coreCtx coreState₀
  pure res

structure Rendered where
  constants : List (String × SExpr)
  functions : Std.HashMap String SExpr
  structures : Std.HashMap String SExpr

def renderIR (ir : Translations String) : Rendered × SExprState :=
  let (res, postState) := SExprM.run 2 ir do
    let mut constants := []
    let mut functions := Std.HashMap.emptyWithCapacity
    let mut structures := Std.HashMap.emptyWithCapacity

    for (name, structDef) in ir.structures.toList do
      let s ← structDef.toSExpr
      structures := structures.insert name s

    for (name, funcDef) in ir.functions.toList do
      let f ← funcDef.toSExpr
      if funcDef.parameters.isEmpty then
        constants := (name, f) :: constants
      else
        functions := functions.insert name f
    pure (Rendered.mk constants functions structures)

  (Rendered.mk (sortConstantsTopologically postState res.constants) res.functions res.structures, postState)

def elispPrelude : String := include_str "Extractor/prelude.el"

def renderIntermediate (targetFile : System.FilePath) (translations : Translations String) : IO Unit := do
  let rawHdl ← IO.FS.Handle.mk targetFile IO.FS.Mode.write
  for (_name, ind) in translations.inductives.toList do
    rawHdl.putStrLn (reprStr ind)

  for (_name, func) in translations.functions.toList do
    rawHdl.putStrLn (reprStr func)

def renderToFile (targetFile : System.FilePath) (rendered : Rendered) : IO Unit := do
  let hdl ← IO.FS.Handle.mk targetFile IO.FS.Mode.write

  hdl.putStrLn ";;; lgtm-lean-core.el --- Extracted LgtmLean core -*- lexical-binding: t; -*-"
  hdl.putStrLn ";; This file is generated by extracting Lean code. Do not edit this file directly."
  hdl.putStrLn ""
  hdl.putStrLn "(require 'cl-lib)"
  hdl.putStrLn "(require 'seq)"
  hdl.putStrLn "(require 'subr-x)"
  hdl.putStrLn ""
  hdl.putStrLn ";;; Code:"
  hdl.putStrLn ""
  hdl.putStrLn ";; Type definitions"

  -- We have to emit the type definitions at the top of the file since they define macros that must be visible
  -- by the time the functions are defined to avoid runtime errors.
  for (_, structSExpr) in rendered.structures.toList.mergeSort (·.1 ≤ ·.1) do
    hdl.putStrLn (structSExpr.render)
    hdl.putStrLn ""

  hdl.putStrLn ";; Prelude"
  hdl.putStrLn ""

  hdl.putStrLn elispPrelude
  hdl.putStrLn ""

  hdl.putStrLn ";; Constants"
  hdl.putStrLn ""

  for (_, constant) in rendered.constants do
    hdl.putStrLn constant.render
    hdl.putStrLn ""

  hdl.putStrLn ";; Functions"
  hdl.putStrLn ""

  for (_, funcSExpr) in rendered.functions.toList.mergeSort (·.1 ≤ ·.1) do
    hdl.putStrLn (funcSExpr.render)
    hdl.putStrLn ""

unsafe def extractLgtm : IO (Translations String × Rendered × SExprState) := do
  -- `loadExts` defaults to `false`, which leaves environment extensions unpopulated from the
  -- imported `.olean`s, even though the declarations themselves are visible. Without it,
  -- `translateFunction` intermittently fails to translate a recursive function with "no progress at
  -- goal", not because the function is untranslatable, but because the equation-lemma generator was
  -- missing the very state that made generation succeed when the same declaration is queried from
  -- inside its own file (e.g. via `#print equations`). `enableInitializersExecution` is `loadExts
  -- := true`'s own prerequisite.
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `LgtmLean }] {} (trustLevel := 1024) (loadExts := true)

  let translations ← runMeta env (translateLeanDefinitions env)
  let (rendered, postState) := renderIR translations

  pure (translations, rendered, postState)

