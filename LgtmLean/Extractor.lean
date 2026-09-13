import Lean
import LgtmLean

import Extractor.IR
import Extractor.Render

open Lean

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

/-- Whether `name` is a structure definition -- an inductive registered with Lean's structure
machinery (so it has exactly one constructor and projection functions for its fields) -- as
opposed to a plain enum/inductive, function, theorem, or other kind of declaration. -/
def isStructureDecl (env : Environment) (name : Name) : ConstantInfo → Bool
  | .inductInfo _ => Lean.isStructure env name
  | _ => false

/-- Whether `name` is a plain inductive definition -- an enum or algebraic data type -- as opposed
to a structure (handled separately by `isStructureDecl`/`translateStructure`), function, theorem,
or other kind of declaration. -/
def isInductiveDecl (env : Environment) (name : Name) : ConstantInfo → Bool
  | .inductInfo _ => !Lean.isStructure env name
  | _ => false

/-- Whether `name` is a declaration the compiler generated on our behalf (structure/inductive
machinery, equation lemmas, proof-irrelevant subterms, etc.) rather than something a person wrote.

Deliberately only inspects `name`'s own last component, not `Name.isInternalDetail` (which also
inspects the *prefix* for numeric components) -- under the module system, an ordinary
(non-`public`) declaration is itself stored with a numeric component in its prefix (see
`isLgtmLeanDecl`), which would make `isInternalDetail` flag every such declaration as generated. -/
def isCompilerGenerated (env : Environment) (name : Name) : Bool :=
  let hasBadLastComponent :=
    match name with
    | .str _ s =>
      s == "ctorIdx" || s == "ctorElimType" || s == "below" || s == "ibelow" || s == "ofNat" || s == "toCtorIdx" ||
        s.startsWith "_" || s.startsWith "eq_" || s.startsWith "match_" || s.startsWith "proof_" ||
        s.startsWith "omega_" || s.endsWith "_flat_ctor" || s.startsWith "sizeOf_spec" ||
        s.endsWith "noConfusionType" || s.startsWith "inst" || s.endsWith "decidable"
    | _ => true
  -- Catches instance-dictionary field projections (e.g. `instBEqFoo.beq`) and `match_N.splitter`
  -- helpers, whose *own* last component looks ordinary but whose parent doesn't.
  let hasBadParentComponent :=
    match name.getPrefix with
    | .str _ s => s.startsWith "inst" || s.startsWith "match_"
    | _ => false
  Lean.isAuxRecursor env name || Lean.isNoConfusion env name || env.isProjectionFn name ||
    Lean.Meta.isInstanceCore env name || hasBadLastComponent || hasBadParentComponent

/-

# Overall design of the extractor

The extractor traverses function and type definitions to render them as elisp functions and definitions.

- All of the extracted functions will be private/internal elisp (i.e., prefixed with lgtm--)
- The extractor will maintain a list of names deemed public and to be prefixed with `lgtm-` to denote that they are available for users of the lgtm library
- No values or definitions in `Prop` will be exported, as they have no run-time representation
- Translation of functions will go through a simplified intermediate AST

-/

/-! ## A simple lambda calculus, suitable as a translation target for Lisp -/


/-! ## Erasure -/

/-- Whether a value of type `ty` has no run-time representation: `ty` is a `Prop` (so the value is
a proof), `ty` is itself a `Sort` (so the value is a type, e.g. an implicit `{α : Type}` argument),
or `ty` is a type class other than `Decidable` (so the value is a typeclass dictionary, e.g. `[BEq
α]`/`[Hashable α]`). `Decidable` is deliberately excluded: elsewhere in the pipeline (`Decidable.decide`,
the `if`/`ite`/`cond` lifting of Prop-valued conditions to `Bool`) a `Decidable p` value is treated
as the actual computed answer, not a dispatch table, so erasing it would delete the very data those
call sites need. Every other class in this codebase (`BEq`, `Hashable`, `Min`, `Max`, `HAdd`, ...)
is used purely for dispatch -- the special-cased builtins in `Render.lean` that need one of its
methods (e.g. `BEq.beq`, `Std.HashMap.insert`) call straight through to elisp's own structural
equality/hashing instead, so the dictionary itself never needs to survive to the rendered output.
Defensively returns `false` (i.e. "keep it") if type inference gets stuck, rather than taking down
the whole translation. -/
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

/-- Whether `n`'s own last name component looks like an auto-generated matcher name (`match_1`,
`match_2`, ...). Mirrors the heuristic `Lean.Meta.Match.Extension.getMatcherInfo?` uses
internally; we can't reuse that function (nor `Lean.Meta.matchMatcherApp?`, which is built on it)
directly, because its backing environment extension only exports entries for `public` declarations
-- it never finds anything for `LgtmLean`'s own (all module-private) matchers, even under
`import all`. `tryDecodeMatcher` below reimplements the equivalent decoding directly against the
matcher's raw `Expr` value instead. -/
def isLikelyMatcherName (n : Name) : Bool :=
  match n.eraseMacroScopes with
  | .str _ s => s.startsWith "match_"
  | _ => false

/-- Whether `s` is a Lean-generated name for a genuinely-unused, inaccessible binder (rendered with
`✝`). Unlike a merely hygienic name (containing `._@.`, which can still be a used, ordinary
variable -- e.g. an equation lemma's passed-through, non-pattern-matched argument), this is a
reliable "definitely unused" signal. -/
def looksInaccessible (s : String) : Bool :=
  s.any (· == '✝')

/-- Replace each `LPat.var` placeholder in `p` with the next name pulled off `queue`, threading the
remaining queue through. Inaccessible names become `LPat.wildcard` instead of a `var` so the result
doesn't invent a bogus binder name for something genuinely unused. -/
partial def relabelPat (p : LPat) (queue : List String) : LPat × List String :=
  match p with
  | .var _ =>
    match queue with
    | [] => (.wildcard, [])
    | n :: rest => ((if looksInaccessible n then .wildcard else .var n), rest)
  | .ctor name fields =>
    let (fields', queue') := fields.foldl (fun (acc, q) f =>
      let (f', q') := relabelPat f q
      (acc ++ [f'], q')) ([], queue)
    (.ctor name fields', queue')
  | other => (other, queue)

def relabelPats (pats : List LPat) (queue : List String) : List LPat × List String :=
  pats.foldl (fun (acc, q) p =>
    let (p', q') := relabelPat p q
    (acc ++ [p'], q')) ([], queue)

/-! ## Translation of `Expr` into `LExpr` / `LPat`

Two independent mechanisms produce patterns, corresponding to the two ways Lean elaborates
pattern matching:

* A recursive (or otherwise multi-clause) top-level function is compiled via well-founded or
  structural recursion, which is very hard to decode faithfully from its raw `Expr` value. Instead
  `translateFunction` reads off Lean's auto-generated *equation lemmas* (`f.eq_1`, `f.eq_2`, ...),
  whose statement `∀ xs, f pat₁ ... patₙ = rhs` already exposes exactly the patterns and right-hand
  sides written at the definition site (see `exprToPat`).
* A `match ... with` expression occurring *inside* a body (whether that body came from an
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
.. | n+1 => ..`), since Lean still needs *some* name for the parameter in `f`'s own type --
`translateFunction` uses this to reject that pattern-bound function definition form, which
`LFunction`'s flat `parameters : List String` cannot represent. It also happens, harmlessly, for an
anonymous instance-implicit binder (e.g. `[BEq α]`), but `translateFunction` never checks this
function against those: `isErasableType` erases every instance-implicit parameter before its name
would ever be examined. -/
def isElaboratorGeneratedName (n : Name) : Bool :=
  n.hasMacroScopes

/-- A stable, Lisp-safe name for a parameter binder. Falls back to a synthetic name when the
binder's own name was invented by the elaborator (see `isElaboratorGeneratedName`) -- which
happens for eta-expansion's own synthesized trailing parameters (see `translateApp`), since those
don't come from any real source-level binder. -/
def paramNameOrFallback (n : Name) (idx : Nat) : String :=
  if isElaboratorGeneratedName n then s!"etaArg{idx}" else toString n

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
      let varNames' := varNames.insert fvar.fvarId! (toString n)
      let bL ← translateExpr varNames' (b.instantiate1 fvar)
      if erase then
        pure bL
      else
        let vL ← translateExpr varNames v
        pure (.letE (toString n) vL bL)
  | .lam .. =>
    Meta.lambdaTelescope e fun xs body => do
      let mut varNames' := varNames
      let mut paramNames : List String := []
      for x in xs do
        let ld ← x.fvarId!.getDecl
        let nm := toString ld.userName
        varNames' := varNames'.insert x.fvarId! nm
        if !(← isErasableType ld.type) then
          paramNames := paramNames ++ [nm]
      let bodyL ← translateExpr varNames' body
      pure (.lam paramNames bodyL)
  | .app .. => translateApp varNames e
  | .const n _ => translateConstRef n
  | _ => pure (.opaque s!"unsupported term shape")

/-- Translate a (possibly under-saturated) application. If `e`'s own type is still a function
type -- i.e. `e` is a first-class partially-applied value, such as a bare global reference passed
to `List.map` -- eta-expand it into an explicit `LExpr.lam` over the remaining parameters before
translating, since Lisp targets don't support Lean's implicit currying: an elisp `defun` called
with fewer arguments than it declares is a runtime arity error, not a closure. Otherwise, first
checks whether the head looks like an auto-generated matcher and, if so, tries to decode it into
`LExpr.matchE`; otherwise (or if decoding fails) falls back to translating it as an ordinary call,
erasing `Prop`/`Sort` arguments and special-casing the two-branch `cond`/`ite` primitives into
`LExpr.ite`. -/
partial def translateApp (varNames : Std.HashMap FVarId String) (e : Expr) : Meta.MetaM LExpr := do
  let eType ← Meta.whnf (← Meta.inferType e)
  if eType.isForall then
    Meta.forallTelescope eType fun tailXs _ => do
      let mut varNames' := varNames
      let mut tailNames : List String := []
      for x in tailXs do
        let ld ← x.fvarId!.getDecl
        unless ← isErasableType ld.type do
          let nm := paramNameOrFallback ld.userName tailNames.length
          varNames' := varNames'.insert x.fvarId! nm
          tailNames := tailNames ++ [nm]
      let bodyL ← translateApp varNames' (mkAppN e tailXs)
      pure (.lam tailNames bodyL)
  else
    e.withApp fun fn args => do
      let matcherResult? ← match fn with
        | .const cName _ =>
          if isLikelyMatcherName cName then tryDecodeMatcher varNames cName args else pure none
        | _ => pure none
      match matcherResult? with
      | some r => pure r
      | none => do
        -- A field whose own value is itself a function (e.g. `Configuration.createComment :
        -- Configuration → Comment → Option ServerId`) can appear applied to more arguments than
        -- just the structure instance: `config.createComment comment`. Lean's currying makes this
        -- indistinguishable, at the `Expr` level, from an ordinary two-parameter function
        -- application -- but the elisp target isn't: `Configuration.createComment` compiles to a
        -- `cl-defstruct` accessor of arity exactly one. Splitting off the field access from the
        -- extra arguments (which get funcall'd onto the result, see `LExpr.toSExpr`'s `.proj` case
        -- in `Render.lean`) keeps that arity correct. Class-method projections (`BEq.beq` and
        -- friends) are excluded since those are already special-cased whole in
        -- `translatePrimitives`, which expects them pre-flattened.
        let projResult? ← match fn with
          | .const cName _ => do
            match ← getProjectionFnInfo? cName with
            | some info =>
              if !info.fromClass && info.numParams + 1 < args.size then
                let structName := info.ctorName.getPrefix
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
          let mut keptArgs : List LExpr := []
          for a in args do
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

`matcherName`'s own (uninstantiated) value has the shape
`fun params motive discrs alts => <tree of casesOn on the discrs>`, with the tree's leaves being
bare applications of one of the `alts` binders. We walk that tree once (`walkMatcherBody`) to
recover, per leaf, which discriminants were scrutinized -- to what nested depth, under which
constructors -- to reach it; the real per-alternative bodies (with real bound-variable names) are
then read off of `args` at the corresponding position, not out of the generic tree. Returns `none`
(falling back to ordinary call translation) if `matcherName` isn't actually a matcher-shaped
definition, e.g. because it doesn't delta-reduce to a recognizable `casesOn` tree at all.

A discriminant position whose *type* is erasable (e.g. a `Prop` destructured purely to unpack proof
obligations, as in `let ⟨hFound, ...⟩ := hAll entry mem⟩`) is dropped from the emitted pattern
rather than rendered as a real `pcase` branch: Lean's kernel only allows eliminating a `Prop` into a
data-sorted result -- which is exactly what's happening here, since the matcher produces this
function's real return value -- when the eliminated type is a subsingleton (at most one
constructor), so every row sharing that position is definitionally forced to the same shape. If
*every* discriminant turns out to be erasable this way, there is (by the same argument) exactly one
reachable row, so the whole match collapses to that row's body translated directly, with no `pcase`
at all. -/
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
          varNames' := varNames'.insert rx.fvarId! (toString ld.userName)
        some <$> translateExpr varNames' realBody
    else
      let discrExprs ← keptPositions.mapM (fun p => translateExpr varNames args[p]!)
      let mut alts : List (List LPat × LExpr) := []
      for (assoc, altFv) in rows do
        let some altPos := topPos[altFv]? | continue
        let altArgExpr := args[altPos]!
        let clause ← Meta.lambdaTelescope altArgExpr fun realXs realBody => do
          let mut varNames' := varNames
          let mut nameStrs : List String := []
          for rx in realXs do
            let ld ← rx.fvarId!.getDecl
            let nm := toString ld.userName
            varNames' := varNames'.insert rx.fvarId! nm
            nameStrs := nameStrs ++ [nm]
          let bodyL ← translateExpr varNames' realBody
          -- Several entries in `assoc` can share the same root position `p` -- one per depth of
          -- nesting scrutinized under it -- so fold them into `p`'s pattern shallowest-first,
          -- inserting each deeper `ctor` into the placeholder its immediate parent already reserved.
          -- Relabeling walks *every* position (not just the kept ones) in the same order the names
          -- were bound in, so the queue stays aligned; only afterwards do we drop the erased
          -- positions' (now-irrelevant) patterns from what's actually emitted.
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

/-- Walk a matcher's own generic `casesOn` tree. Returns one row per leaf reached: the assoc-list
of (root discriminant position, path of ctor-field indices from that root, constructor pattern at
that path) accumulated on the way there, plus the `FVarId` (one of `topPos`'s keys) of the
alternative binder applied at that leaf. A discriminant (or field of one) that's never destructured
on some path (e.g. a wildcard `_` pattern) simply doesn't appear in that row's assoc-list;
`tryDecodeMatcher` pads for this using the union of root positions seen across all rows, and
defaults any un-visited field within a visited root to a plain variable.

A named/dependent match (`match h : e with`) makes the matcher's motive depend on the scrutinee
equality, so the elaborator wraps the real `casesOn` tree in an extra redex --
`(fun x_1 => casesOn ... x_1 ...) x (Eq.refl x)` -- to thread that equality proof through. `headBeta`
strips exactly that wrapper (without unfolding any definitions, unlike `whnf`) so the `casesOn` node
underneath is still recognized; it's a no-op everywhere else. -/
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
both cases uniformly via an empty vs. non-empty path): it may instead be a field variable this
same function bound while decomposing an *enclosing* `casesOn`, which is what makes a source
pattern like `((.topLevel, _), _)` -- nested two constructors deep on a single discriminant --
decodable at all, since Lean compiles it into one matcher whose body chains `casesOn` nodes
directly rather than delegating the inner level to its own auxiliary matcher. -/
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

/-- Decompose one `dite (scrutinee = lit) inst thenBranch elseBranch` node -- how Lean compiles a
`match` against a literal value (`Nat`, `String`, or -- since `Char` has no constructors of its own
-- `Char.ofNat n`) instead of against a genuine inductive constructor -- into a `(rootPos, path,
LPat.lit ..)` row for the positive branch, chained with whatever `elseBranch` (the next `dite` in
the chain, or the final wildcard alt) contributes.

`thenBranch`'s value is `@Eq.ndrec_symm α lit motive (h Unit.unit) scrutinee`: since
`Eq.ndrec_symm`'s own signature is `.. → motive a → {b} → b = a → motive b`, this partial
application (5 of its 6 explicit args) already has exactly the function type `dite` needs for its
`t : cond → α` argument, with no further eta-expansion -- so the leaf alt-binder is its own 4th
explicit argument (`h Unit.unit`), not something reached via `lambdaTelescope`. Literal patterns
carry no field data, so unlike `decomposeCasesOn`'s constructor branches, that binder is applied to
a throwaway `Unit.unit` rather than to any real fields. Only recognizes the scrutinee-on-the-left
equality order actually produced for `LgtmLean`'s own literal matches; anything else falls back
(returns `[]`) to ordinary call translation, same as an unrecognized `casesOn` shape. -/
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

/-- Whether equation clause `pats` is nothing more than the trivial variable patterns naming
`params`, in order -- i.e. the clause doesn't actually destructure any of its arguments. When it's
the sole clause, `translateFunction` uses its body directly instead of wrapping it in a
(redundant) single-alternative `LExpr.matchE`. -/
def isTrivialClause (pats : List LPat) (params : List String) : Bool :=
  pats.length == params.length && (pats.zip params).all fun (p, n) =>
    match p with
    | .var m => m == n
    | _ => false

/-- Translate a single top-level `LgtmLean` function into its `LFunction` representation.

Reads the function's parameter names directly off its own declared type, throwing if any *kept*
(non-erasable, see `isErasableType`) parameter's name was invented by the elaborator rather than
written by the user (see `isElaboratorGeneratedName`) -- that only happens for the pattern-bound
function definition form, which `LgtmLean` no longer uses. An *erasable* parameter's name doesn't
matter (it's dropped either way), so an anonymous instance-implicit binder like `[BEq α]` -- whose
elaborator-invented name would otherwise also trip this guard -- never reaches the check at all.
The body then prefers Lean's auto-generated equation lemmas (one clause per equation) -- this is
what lets recursive functions come through as ordinary pattern matching instead of the raw
well-founded/structural recursion combinators they actually compile to -- falling back to directly
reading off `lambdaTelescope` of the definition's value for functions with no equations (e.g. a
one-line non-recursive `def` with no internal `match`). Multiple equation clauses (or a single
clause that does destructure its arguments, e.g. a single-constructor structure) are recombined
into one `LExpr.matchE` over the declared parameters. -/
def translateFunction (name : Name) : Meta.MetaM LFunction := do
  let info ← getConstInfo name
  let docstring ← findDocString? (← getEnv) name
  let paramNames ← Meta.forallTelescope info.type fun xs _ => do
    let mut names : List String := []
    for x in xs do
      let ld ← x.fvarId!.getDecl
      unless ← isErasableType ld.type do
        if isElaboratorGeneratedName ld.userName then
          throwError s!"{name} binds a parameter via a pattern instead of a name"
        names := names ++ [toString ld.userName]
    pure names
  match ← Meta.getEqnsFor? name with
  | some eqns => do
    let mut clauses : List (List LPat × LExpr) := []
    for eqnName in eqns do
      let eqnInfo ← getConstInfo eqnName
      let clause ← Meta.forallTelescope eqnInfo.type fun xs eqType => do
        let mut varNames : Std.HashMap FVarId String := {}
        for x in xs do
          let ld ← x.fvarId!.getDecl
          varNames := varNames.insert x.fvarId! (toString ld.userName)
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
    let body := match clauses with
      | [(pats, bodyL)] =>
        if isTrivialClause pats paramNames then bodyL else .matchE (paramNames.map LExpr.var) clauses
      | _ => .matchE (paramNames.map LExpr.var) clauses
    pure { name := toString name, parameters := paramNames, body, docstring }
  | none =>
    match info.value? with
    | none =>
      let body := LExpr.opaque "no definition available"
      pure { name := toString name, parameters := paramNames, body, docstring }
    | some v =>
      Meta.lambdaTelescope v fun xs body => do
        let mut varNames : Std.HashMap FVarId String := {}
        for x in xs do
          let ld ← x.fvarId!.getDecl
          varNames := varNames.insert x.fvarId! (toString ld.userName)
        let bodyL ← translateExpr varNames body
        pure { name := toString name, parameters := paramNames, body := bodyL, docstring }

-- Regression test: `LgtmLean.Files.parseFileModificationType` matches its `Char` parameter against
-- literal patterns (`'M'`, `'A'`, ...). Since it's non-recursive, `translateFunction` takes this
-- function's equation-lemma path, converting each equation's left-hand-side argument via
-- `exprToPat` -- as opposed to the *matcher*-decoding path (`tryDecodeMatcher`/
-- `decomposeDiteLiteral`), used only for a `match` nested inside a larger body. `exprToPat` once
-- had no case for a `Char` literal (represented as the application `Char.ofNat n`, not a bare
-- `Expr.lit`) and silently fell back to `.wildcard` instead of `.lit (.char _)`, which -- since
-- `pcase` tries alternatives in order -- made every character match the first alternative.
/-- info: "LPat.lit (LLit.char 'M'), LPat.lit (LLit.char 'A'), LPat.lit (LLit.char 'D'), LPat.lit (LLit.char 'T'), LPat.lit (LLit.char 'R'), LPat.lit (LLit.char 'C'), LPat.var \"c\"" -/
#guard_msgs in
#eval show Meta.MetaM String from do
  let f ← translateFunction `parseFileModificationType
  match f.body with
  | .matchE _ alts => pure (", ".intercalate (alts.map (fun (pats, _) => reprStr pats.head!)))
  | _ => pure "no matchE"

/-- Whether `name`'s own declared type has no run-time representation once its full arrow
telescope is peeled off: either a `Prop` (a proof-producing predicate like
`SelectedComment.WellFormed`) or itself a `Sort` (a type synonym like `abbrev CommentThread := ...`).
Neither is really a "function" in the run-time sense -- translating its body would just erase
everything down to a meaningless husk, so `main` skips these outright rather than emitting one. -/
def isPropReturningDecl (name : Name) : Meta.MetaM Bool := do
  try
    Meta.forallTelescope (← getConstInfo name).type fun _ codomain => isErasableType codomain
  catch _ =>
    return false

/-- Whether the inductive `name`, once its indices/parameters are peeled off, is itself the `Prop`
sort -- i.e. it's a proof-only relation (like `CommentThreads.NodeReachable`) rather than a genuine
data type. Checks `codomain.isProp` (is this expression *literally* the sort `Prop`), not
`Meta.isProp codomain` (is the *type of* this expression `Prop`, which asks a different question
here since `codomain` is itself a classifying sort, not a value). Also deliberately does not treat
a `Type`-valued codomain as erasable the way `isPropReturningDecl` does for functions: every
ordinary data inductive's own declared type is itself `Type`-sorted (that's just what it means to
be a type), so that check would reject every inductive, not just the proof-only ones. -/
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
    for x in xs do
      let ld ← x.fvarId!.getDecl
      unless ← isErasableType ld.type do
        fields := fields ++ [toString ld.userName]
    pure { name := toString name, fields }

/-- Translate a single top-level `LgtmLean` (non-structure) inductive into its
`LInductiveDefinition` representation: one `(name, arity)` pair per constructor, where the arity
discards any constructor field of an erasable type (e.g., Prop) -- mirroring `translateStructure`. -/
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

/-- The number of `constantNames` not yet in `visiting`. Used only as the termination measure for
`visitConstantForTopoSort`/`visitConstantsForTopoSort`: visiting a new name (one drawn from
`constantNames` and not already in `visiting`) strictly shrinks this, which is what
`remaining_insert_lt` below establishes. -/
private def remaining (constantNames visiting : Std.HashSet String) : Nat :=
  (constantNames.toList.filter (fun n => !visiting.contains n)).length

private theorem remaining_insert_lt (constantNames visiting : Std.HashSet String) (name : String)
    (hMem : name ∈ constantNames) (hNotVisiting : ¬ visiting.contains name) :
    remaining constantNames (visiting.insert name) < remaining constantNames visiting := by
  unfold remaining
  have hEq : (constantNames.toList.filter (fun n => !(visiting.insert name).contains n))
      = (constantNames.toList.filter (fun n => !visiting.contains n)).filter (fun n => !(name == n)) := by
    rw [List.filter_filter]
    congr 1
    funext n
    simp [Std.HashSet.contains_insert, Bool.not_or]
  rw [hEq, List.length_filter_lt_length_iff_exists]
  refine ⟨name, ?_, ?_⟩
  · rw [List.mem_filter]
    exact ⟨Std.HashSet.mem_toList.mpr hMem, by simp [hNotVisiting]⟩
  · simp

mutual

/-- Depth-first, postorder visit of `name` in the dependency graph implied by `calledGlobalNames`,
restricted to edges landing on another constant (a reference to an ordinary function doesn't
constrain ordering, since a `defun` body isn't evaluated until it's called, unlike a `defconst`
initializer). Appends every dependency to `acc` before `name` itself, so nothing ever precedes
something it depends on; `visited` (threaded across the whole traversal) keeps each constant from
being emitted twice, while `visiting` (reset per top-level start, extended going down) tracks the
current path so a genuine dependency cycle -- which shouldn't arise for well-formed top-level
`LgtmLean` constants, since a Lean `def`'s value can only reference declarations that already exist
-- gets silently broken rather than looping forever.

The `constantNames.contains name` guard is a no-op for every real caller (both `sortConstantsTopologically`
and the recursive call below only ever pass a `name` drawn from `constantNames`), added solely so
the termination measure (`remaining`, strictly decreasing on every genuine visit) is total and
provable without threading an extra membership hypothesis through the signature. -/
def visitConstantForTopoSort (calledGlobalNames : Std.HashMap String (Std.HashSet String))
    (constantNames : Std.HashSet String) (name : String) (visiting : Std.HashSet String)
    (visited : Std.HashSet String) (acc : List String) : Std.HashSet String × List String :=
  if hcn : constantNames.contains name then
    if hvv : visited.contains name || visiting.contains name then
      (visited, acc)
    else
      let deps := (calledGlobalNames.getD name Std.HashSet.emptyWithCapacity).toList.filter constantNames.contains
      let (visited', acc') :=
        visitConstantsForTopoSort calledGlobalNames constantNames deps (visiting.insert name) visited acc
      (visited'.insert name, acc' ++ [name])
  else
    (visited, acc)
termination_by (remaining constantNames visiting, 0)
decreasing_by
  simp only [Bool.or_eq_true, not_or] at hvv
  have hMem : name ∈ constantNames := Std.HashSet.mem_iff_contains.mpr hcn
  have hNotVisiting : ¬ visiting.contains name := by simpa using hvv.2
  have := remaining_insert_lt constantNames visiting name hMem hNotVisiting
  simp_all
  omega

/-- Visit each dependency in `deps` in turn (threading `visited`/`acc` through), the list-recursive
half of `visitConstantForTopoSort`'s mutual recursion -- broken out as its own function (rather than
a `List.foldl`) purely so Lean's termination checker can see the recursive calls directly. -/
def visitConstantsForTopoSort (calledGlobalNames : Std.HashMap String (Std.HashSet String))
    (constantNames : Std.HashSet String) (deps : List String) (visiting : Std.HashSet String)
    (visited : Std.HashSet String) (acc : List String) : Std.HashSet String × List String :=
  match deps with
  | [] => (visited, acc)
  | dep :: rest =>
    let (visited', acc') := visitConstantForTopoSort calledGlobalNames constantNames dep visiting visited acc
    visitConstantsForTopoSort calledGlobalNames constantNames rest visiting visited' acc'
termination_by (remaining constantNames visiting, deps.length)
decreasing_by
  all_goals simp_all; omega

end

/-- Use the `calledGlobalNames` field of `postTranslationState` to topologially sort the list of constants.

Several constant initializers refer to other constants in their initializers.  Constants in elisp
must be defined before they are referenced.  `calledGlobalNames` records which constant initializer
refers to which other constants.

-/
def sortConstantsTopologically (postTranslationState : SExprState) (constants : List (String × SExpr)) :
    List (String × SExpr) :=
  let constantMap : Std.HashMap String SExpr :=
    constants.foldl (fun m (name, sexpr) => m.insert name sexpr) Std.HashMap.emptyWithCapacity
  let constantNames : Std.HashSet String :=
    constants.foldl (fun s (name, _) => s.insert name) Std.HashSet.emptyWithCapacity
  let (_, orderedNames) := constants.foldl
    (fun (visited, acc) (name, _) =>
      visitConstantForTopoSort postTranslationState.calledGlobalNames constantNames name
        Std.HashSet.emptyWithCapacity visited acc)
    (Std.HashSet.emptyWithCapacity, [])
  orderedNames.filterMap (fun name => (constantMap[name]?).map (name, ·))

def renderIR (ir : Translations String) : Rendered :=
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

  Rendered.mk (sortConstantsTopologically postState res.constants) res.functions res.structures

def elispPrelude : String := include_str "Extractor/prelude.el"

unsafe def main (args : List String) : IO Unit := do
  let targetFile ← if hArgs : args.length ≠ 1 then
      throw (IO.userError "The path to an elisp file to generate is a required argument")
    else
      pure (System.FilePath.mk (args[0]'(by omega)))

  -- `loadExts` defaults to `false`, which leaves environment extensions -- including the
  -- `Structural`/`WF` `EqnInfo` that `Meta.getEqnsFor?` needs to lazily regenerate equation lemmas
  -- for recursive functions -- unpopulated from the imported `.olean`s, even though the
  -- declarations themselves are visible. Without it, `translateFunction` intermittently fails to
  -- translate a recursive function with "no progress at goal", not because the function is
  -- untranslatable, but because the equation-lemma generator was missing the very state that made
  -- generation succeed when the same declaration is queried from inside its own file (e.g. via
  -- `#print equations`). `enableInitializersExecution` is `loadExts := true`'s own prerequisite.
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `LgtmLean }] {} (trustLevel := 1024) (loadExts := true)

  let translations ← runMeta env (translateLeanDefinitions env)
  let rendered := renderIR translations

  let rawHdl ← IO.FS.Handle.mk "/tmp/out.txt" IO.FS.Mode.write
  for (_name, ind) in translations.inductives.toList do
    rawHdl.putStrLn (reprStr ind)

  for (_name, func) in translations.functions.toList do
    rawHdl.putStrLn (reprStr func)

  let hdl ← IO.FS.Handle.mk targetFile IO.FS.Mode.write

  hdl.putStrLn ";; This file is generated by extracting Lean code. Do not edit this file directly."
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


private def indexOfConstant (constantName : String) (sortedList : List (String × α)) : Nat :=
  sortedList.findIdx (·.1 == constantName)

/-- `visited.contains x` and `x ∈ acc` agree for every `x`, and `acc` has no duplicates. The
correctness proof threads this through the whole traversal: it's what lets a `visited.contains`
fact (cheap, from a later call's own guard) be converted into an `acc`-membership fact (what we
actually need to reason about position), and back. -/
private def AccInv (visited : Std.HashSet String) (acc : List String) : Prop :=
  (∀ x, visited.contains x ↔ x ∈ acc) ∧ acc.Nodup

section
variable (calledGlobalNames : Std.HashMap String (Std.HashSet String)) (constantNames : Std.HashSet String)
  (rank : String → Nat)
  (hRankEdge : ∀ a b, constantNames.contains a = true → constantNames.contains b = true →
    b ∈ calledGlobalNames.getD a Std.HashSet.emptyWithCapacity → rank b < rank a)

private def filteredDeps (name : String) : List String :=
  (calledGlobalNames.getD name Std.HashSet.emptyWithCapacity).toList.filter constantNames.contains

/-- `d` has already been placed into `acc` at a position with a documented "before" witness: some
prefix `pre` of `acc` already contains every filtered dependency of `d`, without yet containing `d`
itself. Combined with `d ∈ acc`, this is exactly the fact `sortConstantsTopologically.isCorrect`
needs -- `d`'s dependencies precede it -- stated so it can be *carried forward* as `acc` grows
(see `WellPlaced_mono`) rather than re-derived every time. -/
private def WellPlaced (acc : List String) (d : String) : Prop :=
  d ∈ acc ∧ ∃ pre, pre <+: acc ∧ d ∉ pre ∧ ∀ dep ∈ filteredDeps calledGlobalNames constantNames d, dep ∈ pre

/-- `WellPlaced` survives `acc` growing by any prefix-preserving extension: the same "before"
witness `pre` still works against the longer list. This is what lets a name's placement, once
established, remain valid through however much further processing happens afterward -- the crux of
threading it as an ongoing invariant instead of a one-shot fact. -/
private theorem WellPlaced_mono (acc acc' : List String) (hpre : acc <+: acc') (d : String)
    (h : WellPlaced calledGlobalNames constantNames acc d) : WellPlaced calledGlobalNames constantNames acc' d := by
  obtain ⟨hmem, pre, hpreLe, hnotmem, hdeps⟩ := h
  exact ⟨hpre.mem hmem, pre, hpreLe.trans hpre, hnotmem, hdeps⟩

/-- The invariant carried through `visitConstantForTopoSort`'s well-founded recursion (paired with
`motive2` below for `visitConstantsForTopoSort`), proved via `visitConstantForTopoSort.induct`.
Beyond `AccInv`/prefix-monotonicity/frozen-visiting (mirroring the plain termination-measure
argument), the two invariants that make the final correctness theorem provable are:
- `rank name ≤ rank n` for every `n` currently `visiting`: since every edge strictly decreases
  rank (`hRankEdge`), this rules out a filtered dependency ever being a currently-active ancestor
  -- the one scenario that would otherwise stop it from getting placed before `name`.
- the last conjunct: a real (non-skipped) visit leaves `name` itself `WellPlaced`, and every
  already-visited name stays `WellPlaced` (via `WellPlaced_mono` against this call's own prefix
  growth) -- so nothing already placed is ever "un-placed" by later processing. -/
private def motive1 (name : String) (visiting visited : Std.HashSet String) (acc : List String) : Prop :=
  AccInv visited acc → (∀ n, visiting.contains n = true → rank name ≤ rank n) →
  (∀ d, visited.contains d = true → WellPlaced calledGlobalNames constantNames acc d) →
  AccInv (visitConstantForTopoSort calledGlobalNames constantNames name visiting visited acc).1
         (visitConstantForTopoSort calledGlobalNames constantNames name visiting visited acc).2 ∧
  acc <+: (visitConstantForTopoSort calledGlobalNames constantNames name visiting visited acc).2 ∧
  (∀ y, visiting.contains y = true →
     (visitConstantForTopoSort calledGlobalNames constantNames name visiting visited acc).1.contains y = visited.contains y) ∧
  (∀ d, (visitConstantForTopoSort calledGlobalNames constantNames name visiting visited acc).1.contains d = true →
     WellPlaced calledGlobalNames constantNames
       (visitConstantForTopoSort calledGlobalNames constantNames name visiting visited acc).2 d) ∧
  (constantNames.contains name = true → visiting.contains name = false →
     (visitConstantForTopoSort calledGlobalNames constantNames name visiting visited acc).1.contains name = true)

/-- The `visitConstantsForTopoSort` (list-processing) counterpart of `motive1`. `boundRank` bounds
every element of `deps` (all filtered dependencies of some common caller), which is what lets each
recursive visit re-derive its own `rank`-vs-`visiting` invariant from this one. -/
private def motive2 (deps : List String) (visiting visited : Std.HashSet String) (acc : List String) : Prop :=
  ∀ boundRank : Nat, (∀ d ∈ deps, constantNames.contains d = true) → (∀ d ∈ deps, rank d < boundRank) →
    (∀ n, visiting.contains n = true → boundRank ≤ rank n) → AccInv visited acc →
    (∀ d, visited.contains d = true → WellPlaced calledGlobalNames constantNames acc d) →
  AccInv (visitConstantsForTopoSort calledGlobalNames constantNames deps visiting visited acc).1
         (visitConstantsForTopoSort calledGlobalNames constantNames deps visiting visited acc).2 ∧
  acc <+: (visitConstantsForTopoSort calledGlobalNames constantNames deps visiting visited acc).2 ∧
  (∀ y, visiting.contains y = true →
     (visitConstantsForTopoSort calledGlobalNames constantNames deps visiting visited acc).1.contains y = visited.contains y) ∧
  (∀ d, (visitConstantsForTopoSort calledGlobalNames constantNames deps visiting visited acc).1.contains d = true →
     WellPlaced calledGlobalNames constantNames
       (visitConstantsForTopoSort calledGlobalNames constantNames deps visiting visited acc).2 d) ∧
  (∀ d ∈ deps, (visitConstantsForTopoSort calledGlobalNames constantNames deps visiting visited acc).1.contains d = true)

private theorem topoCase1 : ∀ (name : String) (visiting visited : Std.HashSet String) (acc : List String),
    constantNames.contains name = true →
      (visited.contains name || visiting.contains name) = true →
        motive1 calledGlobalNames constantNames rank name visiting visited acc := by
  intro name visiting visited acc hcn hvv hInv _hRV hWP
  rw [visitConstantForTopoSort.eq_1]
  simp only [hcn, hvv]
  refine ⟨hInv, List.prefix_refl acc, fun _ _ => rfl, hWP, ?_⟩
  intro _ hvisiting
  rw [Bool.or_eq_true] at hvv
  rcases hvv with h | h
  · exact h
  · simp [h] at hvisiting

include hRankEdge in
private theorem topoCase2 : ∀ (name : String) (visiting visited : Std.HashSet String) (acc : List String),
    constantNames.contains name = true →
      ¬(visited.contains name || visiting.contains name) = true →
        ∀ (visited' : Std.HashSet String) (acc' : List String),
          visitConstantsForTopoSort calledGlobalNames constantNames
            (filteredDeps calledGlobalNames constantNames name)
            (visiting.insert name) visited acc = (visited', acc') →
          motive2 calledGlobalNames constantNames rank
            (filteredDeps calledGlobalNames constantNames name)
            (visiting.insert name) visited acc →
          motive1 calledGlobalNames constantNames rank name visiting visited acc := by
  intro name visiting visited acc hcn hvv visited' acc' heq ih2 hInv hRankVisiting hWP
  simp only [filteredDeps] at heq ih2
  have hboundDeps1 : ∀ d ∈ filteredDeps calledGlobalNames constantNames name, constantNames.contains d = true := by
    intro d hd
    simp only [filteredDeps, List.mem_filter] at hd
    exact hd.2
  have hboundDeps2 : ∀ d ∈ filteredDeps calledGlobalNames constantNames name, rank d < rank name := by
    intro d hd
    simp only [filteredDeps, List.mem_filter, Std.HashSet.mem_toList] at hd
    exact hRankEdge name d hcn hd.2 hd.1
  have hboundVisiting : ∀ n, (visiting.insert name).contains n = true → rank name ≤ rank n := by
    intro n hn
    rw [Std.HashSet.contains_insert] at hn
    rcases Bool.or_eq_true_iff.mp hn with h | h
    · have heqn : name = n := beq_iff_eq.mp h
      rw [heqn]; omega
    · exact hRankVisiting n h
  simp only [filteredDeps] at hboundDeps1 hboundDeps2
  obtain ⟨hAcc', hPre, hVis, hWP', hCover⟩ := ih2 (rank name) hboundDeps1 hboundDeps2 hboundVisiting hInv hWP
  rw [heq] at hAcc' hPre hVis hWP' hCover
  have hresult : visitConstantForTopoSort calledGlobalNames constantNames name visiting visited acc
      = (visited'.insert name, acc' ++ [name]) := by
    rw [visitConstantForTopoSort.eq_1, dif_pos hcn, dif_neg hvv]
    simp only [heq]
  rw [hresult]
  simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hvv
  have hNameNotVisited : visited.contains name = false := hvv.1
  have hNameNotVisiting : visiting.contains name = false := hvv.2
  have hNameInsertContains : (visiting.insert name).contains name = true := by
    simp [Std.HashSet.contains_insert]
  have hVisitedPrimeName : visited'.contains name = visited.contains name := hVis name hNameInsertContains
  have hNameNotInAccPrime : name ∉ acc' := by
    rw [← hAcc'.1 name, hVisitedPrimeName, hNameNotVisited]
    simp
  have hMemDep : ∀ dep ∈ filteredDeps calledGlobalNames constantNames name, dep ∈ acc' := by
    intro dep hdep
    have := hCover dep hdep
    exact (hAcc'.1 dep).mp this
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro x
    show (visited'.insert name).contains x ↔ x ∈ acc' ++ [name]
    simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, List.mem_append,
      List.mem_singleton, ← hAcc'.1 x]
    constructor
    · rintro (h | h)
      · exact Or.inr h.symm
      · exact Or.inl h
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl h.symm
  · show (acc' ++ [name]).Nodup
    rw [List.nodup_append]
    refine ⟨hAcc'.2, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact fun heq2 => hNameNotInAccPrime (heq2 ▸ ha)
  · show acc <+: acc' ++ [name]
    exact hPre.trans (List.prefix_append _ _)
  · intro y hy
    show (visited'.insert name).contains y = visited.contains y
    rcases Classical.em (y = name) with h | h
    · subst h
      exact absurd hy (by simp [hNameNotVisiting])
    · have hyIns : (visiting.insert name).contains y = true := by
        simp [Std.HashSet.contains_insert, hy]
      have hstep := hVis y hyIns
      rw [Std.HashSet.contains_insert, beq_eq_false_iff_ne.mpr (Ne.symm h), hstep]
      simp
  · intro d hd
    show WellPlaced calledGlobalNames constantNames (acc' ++ [name]) d
    rw [Std.HashSet.contains_insert] at hd
    rcases Bool.or_eq_true_iff.mp hd with h | h
    · have heqd : name = d := beq_iff_eq.mp h
      subst heqd
      refine ⟨by simp, acc', List.prefix_append _ _, hNameNotInAccPrime, hMemDep⟩
    · exact WellPlaced_mono calledGlobalNames constantNames acc' (acc' ++ [name]) (List.prefix_append _ _) d (hWP' d h)
  · intro _hcn2 _hvv2
    show (visited'.insert name).contains name = true
    simp [Std.HashSet.contains_insert]

private theorem topoCase3 : ∀ (name : String) (visiting visited : Std.HashSet String) (acc : List String),
    ¬ constantNames.contains name = true →
      motive1 calledGlobalNames constantNames rank name visiting visited acc := by
  intro name visiting visited acc hcn hInv _hRV hWP
  rw [visitConstantForTopoSort.eq_1]
  simp only [hcn]
  exact ⟨hInv, List.prefix_refl acc, fun _ _ => rfl, hWP, fun hc _ => absurd hc (by decide)⟩

private theorem topoCase4 : ∀ (visiting visited : Std.HashSet String) (acc : List String),
    motive2 calledGlobalNames constantNames rank [] visiting visited acc := by
  intro visiting visited acc boundRank _hcn _hrk _hvis hInv hWP
  rw [visitConstantsForTopoSort.eq_1]
  exact ⟨hInv, List.prefix_refl acc, fun _ _ => rfl, hWP, fun _ h => absurd h List.not_mem_nil⟩

private theorem topoCase5 : ∀ (visiting visited : Std.HashSet String) (acc : List String) (n : String)
    (rest : List String) (visited' : Std.HashSet String) (acc' : List String),
      visitConstantForTopoSort calledGlobalNames constantNames n visiting visited acc = (visited', acc') →
        motive1 calledGlobalNames constantNames rank n visiting visited acc →
          motive2 calledGlobalNames constantNames rank rest visiting visited' acc' →
            motive2 calledGlobalNames constantNames rank (n :: rest) visiting visited acc := by
  intro visiting visited acc n rest visited' acc' heq1 ih1 ih2 boundRank hcnAll hrankAll hvisAll hInv hWP
  have hcnN : constantNames.contains n = true := hcnAll n (List.mem_cons_self)
  have hcnRest : ∀ d ∈ rest, constantNames.contains d = true := fun d hd => hcnAll d (List.mem_cons_of_mem n hd)
  have hrankN : rank n < boundRank := hrankAll n (List.mem_cons_self)
  have hrankRest : ∀ d ∈ rest, rank d < boundRank := fun d hd => hrankAll d (List.mem_cons_of_mem n hd)
  have hvisitingNFalse : visiting.contains n = false := by
    cases hv : visiting.contains n with
    | false => rfl
    | true => exfalso; have := hvisAll n hv; omega
  have hRankVisitingN : ∀ m, visiting.contains m = true → rank n ≤ rank m := by
    intro m hm
    have := hvisAll m hm
    omega
  obtain ⟨hAcc1, hPre1, hVis1, hWP1', hMemN⟩ := ih1 hInv hRankVisitingN hWP
  rw [heq1] at hAcc1 hPre1 hVis1 hWP1' hMemN
  have hresult : visitConstantsForTopoSort calledGlobalNames constantNames (n :: rest) visiting visited acc
      = visitConstantsForTopoSort calledGlobalNames constantNames rest visiting visited' acc' := by
    rw [visitConstantsForTopoSort.eq_2, heq1]
  rw [hresult]
  obtain ⟨hAcc2, hPre2, hVis2, hWP2', hMemRest⟩ := ih2 boundRank hcnRest hrankRest hvisAll hAcc1 hWP1'
  have hnVisited' : visited'.contains n = true := hMemN hcnN hvisitingNFalse
  refine ⟨hAcc2, hPre1.trans hPre2, ?_, hWP2', ?_⟩
  · intro y hy
    rw [hVis2 y hy, hVis1 y hy]
  · intro dep hdep
    rcases List.mem_cons.mp hdep with h | h
    · subst h
      exact (hAcc2.1 dep).mpr (hPre2.mem ((hAcc1.1 dep).mp hnVisited'))
    · exact hMemRest dep h

include hRankEdge in
/-- The main correctness invariant for `visitConstantsForTopoSort`, established by structural
induction over its own well-founded recursion (`.induct`, generated automatically alongside it and
`visitConstantForTopoSort`). See `motive2`'s docstring for what the invariant actually says. -/
private theorem visitConstantsForTopoSort_correct : ∀ (deps : List String) (visiting visited : Std.HashSet String)
    (acc : List String), motive2 calledGlobalNames constantNames rank deps visiting visited acc :=
  visitConstantsForTopoSort.induct calledGlobalNames constantNames
    (motive1 calledGlobalNames constantNames rank) (motive2 calledGlobalNames constantNames rank)
    (topoCase1 calledGlobalNames constantNames rank) (topoCase2 calledGlobalNames constantNames rank hRankEdge)
    (topoCase3 calledGlobalNames constantNames rank) (topoCase4 calledGlobalNames constantNames rank)
    (topoCase5 calledGlobalNames constantNames rank)

end

/-- `sortConstantsTopologically`'s own fold over `constants` (nullary `visitConstantForTopoSort`
calls, one per constant, each restarting `visiting` at `∅`) is exactly `visitConstantsForTopoSort`
applied once to the whole name list -- the correctness proof reduces to a single call this way so
`visitConstantsForTopoSort_correct` applies directly to the top-level computation. -/
private theorem fold_eq_visitConstantsForTopoSort (calledGlobalNames : Std.HashMap String (Std.HashSet String))
    (constantNames : Std.HashSet String) (constants : List (String × SExpr))
    (visited : Std.HashSet String) (acc : List String) :
    constants.foldl
      (fun (visited, acc) (name, _) =>
        visitConstantForTopoSort calledGlobalNames constantNames name Std.HashSet.emptyWithCapacity visited acc)
      (visited, acc)
    = visitConstantsForTopoSort calledGlobalNames constantNames (constants.map Prod.fst)
        Std.HashSet.emptyWithCapacity visited acc := by
  induction constants generalizing visited acc with
  | nil => simp [visitConstantsForTopoSort.eq_1]
  | cons hd tl ih =>
    obtain ⟨name, sexpr⟩ := hd
    simp only [List.foldl_cons, List.map_cons]
    rw [visitConstantsForTopoSort.eq_2]
    obtain ⟨visited', acc'⟩ :=
      visitConstantForTopoSort calledGlobalNames constantNames name Std.HashSet.emptyWithCapacity visited acc
    simp only []
    rw [← ih]

private theorem contains_fold_insert (constants : List (String × SExpr)) (s0 : Std.HashSet String) (x : String) :
    (constants.foldl (fun s (name, _) => s.insert name) s0).contains x
      = (s0.contains x || (constants.map Prod.fst).contains x) := by
  induction constants generalizing s0 with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨name, sexpr⟩ := hd
    simp only [List.foldl_cons, List.map_cons, List.contains_cons]
    rw [ih, Std.HashSet.contains_insert, Bool.beq_comm]
    cases (x == name) <;> cases s0.contains x <;> cases (List.map Prod.fst tl).contains x <;> rfl

private theorem contains_fold_insertMap (constants : List (String × SExpr)) (s0 : Std.HashMap String SExpr)
    (x : String) : (constants.foldl (fun m (name, sexpr) => m.insert name sexpr) s0).contains x
      = (s0.contains x || (constants.map Prod.fst).contains x) := by
  induction constants generalizing s0 with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨name, sexpr⟩ := hd
    simp only [List.foldl_cons, List.map_cons, List.contains_cons]
    rw [ih, Std.HashMap.contains_insert, Bool.beq_comm]
    cases (x == name) <;> cases s0.contains x <;> cases (List.map Prod.fst tl).contains x <;> rfl

private theorem mem_fold_insertMap (constants : List (String × SExpr)) (x : String)
    (hx : x ∈ constants.map Prod.fst) :
    ∃ v, (constants.foldl (fun m (name, sexpr) => m.insert name sexpr) Std.HashMap.emptyWithCapacity)[x]? = some v := by
  have hc : (constants.foldl (fun m (name, sexpr) => m.insert name sexpr) Std.HashMap.emptyWithCapacity).contains x
      = true := by
    rw [contains_fold_insertMap]
    simp [hx]
  rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
  exact Option.isSome_iff_exists.mp hc

/-- If `pre` is a prefix of `l` containing a `p`-match but none of `q`, then `q` (scanned over all
of `l`) can't reach its match before `p` does: this is the "before" witness in `WellPlaced` turned
into an actual index comparison. -/
private theorem findIdx_prefix_lt {α : Type} (l pre : List α) (p q : α → Bool) (hpre : pre <+: l)
    (hq : ∀ x ∈ pre, q x = false) (hp : ∃ b ∈ pre, p b = true) :
    l.findIdx q > l.findIdx p := by
  obtain ⟨suffix, hsuf⟩ := hpre
  subst hsuf
  have hp' : pre.findIdx p < pre.length := List.findIdx_lt_length_of_exists hp
  have heqp : (pre ++ suffix).findIdx p = pre.findIdx p := by
    rw [List.findIdx_append, if_pos hp']
  have hnotEq : pre.findIdx q = pre.length := by
    rw [List.findIdx_eq_length]
    exact hq
  have heqq : (pre ++ suffix).findIdx q = suffix.findIdx q + pre.length := by
    rw [List.findIdx_append, if_neg (by omega)]
  omega

private theorem le_foldr_max (l : List Nat) (x : Nat) (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons hd tl ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with h | h
    · subst h; omega
    · have := ih h; omega

private theorem mem_filterMap_fst {α β γ : Type} [BEq α] (l : List α) (m : α → Option β) (f : α → β → γ)
    (y : γ) (hy : y ∈ l.filterMap (fun name => (m name).map (f name))) :
    ∃ a ∈ l, ∃ b, m a = some b ∧ f a b = y := by
  rw [List.mem_filterMap] at hy
  obtain ⟨a, ha, hf⟩ := hy
  cases h : m a with
  | none => rw [h] at hf; simp at hf
  | some b =>
    rw [h] at hf
    simp only [Option.map_some, Option.some.injEq] at hf
    exact ⟨a, ha, b, h, hf⟩

/-- `hAcyclic` captures the one fact about `calledGlobalNames` that real Lean elaboration
guarantees but its type alone doesn't: a `def`'s value can only reference declarations that already
exist, so declaration order is always a valid ranking function consistent with every dependency
edge. Without some such hypothesis the statement is false -- a direct 2-cycle (`A` calling `B` and
`B` calling `A`, both legal as far as the *types* here are concerned) would force
`sortedList` to place `A` both before and after `B`. -/
private theorem sortConstantsTopologically.isCorrect
  (postTranslationState : SExprState)
  (constants : List (String × SExpr))
  (sortedList : List (String × SExpr))
  (hSortedListIsResult : sortConstantsTopologically postTranslationState constants = sortedList)
  (hAcyclic : ∃ rank : String → Nat, ∀ a b, a ∈ constants.map Prod.fst → b ∈ constants.map Prod.fst →
    b ∈ postTranslationState.calledGlobalNames.getD a Std.HashSet.emptyWithCapacity → rank b < rank a) :
∀ constantName, constantName ∈ constants.map Prod.fst →
  ∀ dependsOn, dependsOn ∈ constants.map Prod.fst → dependsOn ≠ constantName →
    dependsOn ∈ postTranslationState.calledGlobalNames.getD constantName Std.HashSet.emptyWithCapacity →
      indexOfConstant constantName sortedList > indexOfConstant dependsOn sortedList := by
  obtain ⟨rank, hRankEdge0⟩ := hAcyclic
  intro constantName hCN dependsOn hDN hNe hDep
  let constantNames := constants.foldl (fun s (name, _) => s.insert name) Std.HashSet.emptyWithCapacity
  have hCNdef : constantNames = constants.foldl (fun s (name, _) => s.insert name) Std.HashSet.emptyWithCapacity := rfl
  have hContainsIff : ∀ x, constantNames.contains x = true ↔ x ∈ constants.map Prod.fst := by
    intro x
    rw [hCNdef, contains_fold_insert]
    simp
  have hRankEdge : ∀ a b, constantNames.contains a = true → constantNames.contains b = true →
      b ∈ postTranslationState.calledGlobalNames.getD a Std.HashSet.emptyWithCapacity → rank b < rank a := by
    intro a b ha hb hab
    exact hRankEdge0 a b ((hContainsIff a).mp ha) ((hContainsIff b).mp hb) hab
  have hInv0 : AccInv (Std.HashSet.emptyWithCapacity : Std.HashSet String) ([] : List String) :=
    ⟨fun x => by simp, by simp⟩
  have hWP0 : ∀ d, (Std.HashSet.emptyWithCapacity : Std.HashSet String).contains d = true →
      WellPlaced postTranslationState.calledGlobalNames constantNames [] d := by
    intro d hd; simp at hd
  let allNames := constants.map Prod.fst
  let boundRank := (allNames.map rank).foldr max 0 + 1
  have hcnAll : ∀ d ∈ allNames, constantNames.contains d = true := fun d hd => (hContainsIff d).mpr hd
  have hrankAll : ∀ d ∈ allNames, rank d < boundRank := by
    intro d hd
    have := le_foldr_max (allNames.map rank) (rank d) (List.mem_map_of_mem hd)
    omega
  have hvisAll : ∀ n, (Std.HashSet.emptyWithCapacity : Std.HashSet String).contains n = true → boundRank ≤ rank n := by
    intro n hn; simp at hn
  obtain ⟨_, _, _, hWPFinal, hCoverFinal⟩ :=
    visitConstantsForTopoSort_correct postTranslationState.calledGlobalNames constantNames rank hRankEdge allNames
      Std.HashSet.emptyWithCapacity Std.HashSet.emptyWithCapacity [] boundRank hcnAll hrankAll hvisAll hInv0 hWP0
  have hCNvisited : (visitConstantsForTopoSort postTranslationState.calledGlobalNames constantNames allNames
      Std.HashSet.emptyWithCapacity Std.HashSet.emptyWithCapacity []).1.contains constantName = true :=
    hCoverFinal constantName hCN
  obtain ⟨_, pre, hpreLe, hCNnotpre, hpredeps⟩ := hWPFinal constantName hCNvisited
  have hDepFiltered : dependsOn ∈ filteredDeps postTranslationState.calledGlobalNames constantNames constantName := by
    simp only [filteredDeps, List.mem_filter, Std.HashSet.mem_toList]
    exact ⟨hDep, (hContainsIff dependsOn).mpr hDN⟩
  have hDependsOnInPre : dependsOn ∈ pre := hpredeps dependsOn hDepFiltered
  have hSortedEq : sortedList = (visitConstantsForTopoSort postTranslationState.calledGlobalNames constantNames
      allNames Std.HashSet.emptyWithCapacity Std.HashSet.emptyWithCapacity []).2.filterMap
      (fun name => ((constants.foldl (fun m (name, sexpr) => m.insert name sexpr)
        Std.HashMap.emptyWithCapacity)[name]?).map (name, ·)) := by
    rw [← hSortedListIsResult]
    simp only [sortConstantsTopologically, fold_eq_visitConstantsForTopoSort]
    rfl
  obtain ⟨valDep, hvalDepEq⟩ := mem_fold_insertMap constants dependsOn hDN
  have hDepPairMem : (dependsOn, valDep) ∈ pre.filterMap
      (fun name => ((constants.foldl (fun m (name, sexpr) => m.insert name sexpr)
        Std.HashMap.emptyWithCapacity)[name]?).map (name, ·)) := by
    rw [List.mem_filterMap]
    exact ⟨dependsOn, hDependsOnInPre, by simp [hvalDepEq]⟩
  have hPreFilterPrefix : pre.filterMap
      (fun name => ((constants.foldl (fun m (name, sexpr) => m.insert name sexpr)
        Std.HashMap.emptyWithCapacity)[name]?).map (name, ·)) <+: sortedList := by
    rw [hSortedEq]
    obtain ⟨suf, hsuf⟩ := hpreLe
    rw [← hsuf, List.filterMap_append]
    exact List.prefix_append _ _
  have hNotConstantName : ∀ y ∈ pre.filterMap
      (fun name => ((constants.foldl (fun m (name, sexpr) => m.insert name sexpr)
        Std.HashMap.emptyWithCapacity)[name]?).map (name, ·)), (y.1 == constantName) = false := by
    intro y hy
    obtain ⟨a, ha, b, hab, hfab⟩ := mem_filterMap_fst pre _ (fun name => (name, ·)) y hy
    have : y.1 = a := by rw [← hfab]
    rw [this]
    apply beq_eq_false_iff_ne.mpr
    intro heq
    exact hCNnotpre (heq ▸ ha)
  exact findIdx_prefix_lt sortedList
    (pre.filterMap (fun name => ((constants.foldl (fun m (name, sexpr) => m.insert name sexpr)
      Std.HashMap.emptyWithCapacity)[name]?).map (name, ·)))
    (·.1 == dependsOn) (·.1 == constantName)
    hPreFilterPrefix hNotConstantName ⟨(dependsOn, valDep), hDepPairMem, by simp⟩
