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
      s == "ctorIdx" || s == "ctorElimType" || s.startsWith "_" || s.startsWith "eq_" ||
        s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "omega_" ||
        s.endsWith "_flat_ctor" || s.startsWith "sizeOf_spec" || s.endsWith "noConfusionType" ||
        s.startsWith "inst"
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
a proof), or `ty` is itself a `Sort` (so the value is a type, e.g. an implicit `{α : Type}`
argument). Defensively returns `false` (i.e. "keep it") if type inference gets stuck, rather than
taking down the whole translation. -/
def isErasableType (ty : Expr) : Meta.MetaM Bool := do
  try
    if ← Meta.isProp ty then
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

/-- Translate a (fully-applied) application. First checks whether the head looks like an
auto-generated matcher and, if so, tries to decode it into `LExpr.matchE`; otherwise (or if
decoding fails) falls back to translating it as an ordinary call, erasing `Prop`/`Sort` arguments
and special-casing the two-branch `cond`/`ite` primitives into `LExpr.ite`. -/
partial def translateApp (varNames : Std.HashMap FVarId String) (e : Expr) : Meta.MetaM LExpr := do
  e.withApp fun fn args => do
    let matcherResult? ← match fn with
      | .const cName _ =>
        if isLikelyMatcherName cName then tryDecodeMatcher varNames cName args else pure none
      | _ => pure none
    match matcherResult? with
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

/-- Try to decode a call `matcherName args...` into an `LExpr.matchE`.

`matcherName`'s own (uninstantiated) value has the shape
`fun params motive discrs alts => <tree of casesOn on the discrs>`, with the tree's leaves being
bare applications of one of the `alts` binders. We walk that tree once (`walkMatcherBody`) to
recover, per leaf, which discriminant positions were scrutinized under which constructor to reach
it; the real per-alternative bodies (with real bound-variable names) are then read off of `args` at
the corresponding position, not out of the generic tree. Returns `none` (falling back to ordinary
call translation) if `matcherName` isn't actually a matcher-shaped definition, e.g. because it
doesn't delta-reduce to a recognizable `casesOn` tree at all. -/
partial def tryDecodeMatcher (varNames : Std.HashMap FVarId String) (matcherName : Name) (args : Array Expr) :
    Meta.MetaM (Option LExpr) := do
  let some ci := (← getEnv).find? matcherName | return none
  let some matcherVal := ci.value? | return none
  Meta.lambdaTelescope matcherVal fun xs body => do
    if xs.size != args.size then return none
    let mut xsPos : Std.HashMap FVarId Nat := {}
    for i in [0:xs.size] do
      xsPos := xsPos.insert xs[i]!.fvarId! i
    let rows ← walkMatcherBody xsPos body
    if rows.isEmpty then return none
    let allPositions := ((rows.flatMap (fun (assoc, _) => assoc.map Prod.fst)).eraseDups).mergeSort (· ≤ ·)
    if allPositions.isEmpty then return none
    let discrExprs ← allPositions.mapM (fun p => translateExpr varNames args[p]!)
    let mut alts : List (List LPat × LExpr) := []
    for (assoc, altFv) in rows do
      let some altPos := xsPos[altFv]? | continue
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
        let rawPats := allPositions.map (fun p =>
          ((assoc.find? (·.1 == p)).map Prod.snd).getD (.var "_"))
        let (labeledPats, _) := relabelPats rawPats nameStrs
        pure (labeledPats, bodyL)
      alts := alts ++ [clause]
    return some (.matchE discrExprs alts)

/-- Walk a matcher's own generic `casesOn` tree. Returns one row per leaf reached: the assoc-list
of (discriminant position in `xsPos`, constructor pattern) accumulated on the way there, plus the
`FVarId` (one of `xsPos`'s keys) of the alternative binder applied at that leaf. A discriminant
that's never destructured on some path (e.g. a wildcard `_` pattern) simply doesn't appear in that
row's assoc-list; `tryDecodeMatcher` pads for this using the union of positions seen across all
rows. -/
partial def walkMatcherBody (xsPos : Std.HashMap FVarId Nat) (e : Expr) :
    Meta.MetaM (List (List (Nat × LPat) × FVarId)) := do
  match e.getAppFn with
  | .const casesOnName _ =>
    let indName := casesOnName.getPrefix
    if casesOnName == indName ++ `casesOn then
      decomposeCasesOn xsPos indName e
    else
      pure []
  | .fvar fvid => pure (if xsPos.contains fvid then [([], fvid)] else [])
  | _ => pure []

/-- Decompose one `indName.casesOn params motive major minor₁ ... minorₖ` node (`k` = number of
constructors of `indName`, in declaration order) and recurse into each `minorᵢ`, which is a
function of that constructor's fields. Only handles non-indexed inductives (true of every type
`LgtmLean` actually pattern-matches on: `Bool`, `List`, `Option`, `Nat`, and its own plain enums). -/
partial def decomposeCasesOn (xsPos : Std.HashMap FVarId Nat) (indName : Name) (e : Expr) :
    Meta.MetaM (List (List (Nat × LPat) × FVarId)) := do
  match (← getEnv).find? indName with
  | some (.inductInfo indInfo) => do
    let args := e.getAppArgs
    let base := indInfo.numParams + 1 + 1
    if args.size < base + indInfo.ctors.length then return []
    match args[indInfo.numParams + 1]! with
    | .fvar fvid =>
      match xsPos[fvid]? with
      | none => pure []
      | some pos => do
        let mut allRows : List (List (Nat × LPat) × FVarId) := []
        for i in [0:indInfo.ctors.length] do
          let ctorName := indInfo.ctors[i]!
          let minor := args[base + i]!
          let rows ← Meta.lambdaTelescope minor fun fieldVars minorBody => do
            let placeholders := fieldVars.toList.map (fun _ => LPat.var "_")
            let subRows ← walkMatcherBody xsPos minorBody
            pure (subRows.map (fun (assoc, altFv) =>
              ((pos, LPat.ctor (toString ctorName) placeholders) :: assoc, altFv)))
          allRows := allRows ++ rows
        pure allRows
    | _ => pure []
  | _ => pure []

end

/-- Whether `n` was invented by the elaborator rather than written by the user. This happens
exactly when a function parameter is bound via a pattern instead of a plain name (e.g.
`def f : Nat → Nat | 0 => .. | n+1 => ..`), since Lean still needs *some* name for the parameter
in `f`'s own type. `translateFunction` uses this to reject the pattern-bound function definition
form, which `LFunction`'s flat `parameters : List String` cannot represent. -/
def isElaboratorGeneratedName (n : Name) : Bool :=
  n.hasMacroScopes

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

Reads the function's parameter names directly off its own declared type, throwing if any of them
was invented by the elaborator rather than written by the user (see `isElaboratorGeneratedName`) --
that only happens for the pattern-bound function definition form, which `LgtmLean` no longer uses.
The body then prefers Lean's auto-generated equation lemmas (one clause per equation) -- this is
what lets recursive functions come through as ordinary pattern matching instead of the raw
well-founded/structural recursion combinators they actually compile to -- falling back to directly
reading off `lambdaTelescope` of the definition's value for functions with no equations (e.g. a
one-line non-recursive `def` with no internal `match`). Multiple equation clauses (or a single
clause that does destructure its arguments, e.g. a single-constructor structure) are recombined
into one `LExpr.matchE` over the declared parameters. -/
def translateFunction (name : Name) : Meta.MetaM LFunction := do
  let info ← getConstInfo name
  let paramNames ← Meta.forallTelescope info.type fun xs _ => do
    let mut names : List String := []
    for x in xs do
      let ld ← x.fvarId!.getDecl
      if isElaboratorGeneratedName ld.userName then
        throwError s!"{name} binds a parameter via a pattern instead of a name"
      unless ← isErasableType ld.type do
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
    pure { name := toString name, parameters := paramNames, body }
  | none =>
    match info.value? with
    | none => pure { name := toString name, parameters := paramNames, body := .opaque "no definition available" }
    | some v =>
      Meta.lambdaTelescope v fun xs body => do
        let mut varNames : Std.HashMap FVarId String := {}
        for x in xs do
          let ld ← x.fvarId!.getDecl
          varNames := varNames.insert x.fvarId! (toString ld.userName)
        let bodyL ← translateExpr varNames body
        pure { name := toString name, parameters := paramNames, body := bodyL }

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

/-- Translate a single top-level `LgtmLean` structure into its `LStructureDefinition`
representation. Reads the fields directly off the structure's constructor (whose type is
`∀ params, field₁ → field₂ → .. → S params`), skipping the leading `numParams` binders -- the
structure's own type parameters, e.g. `α` in `Tree α` -- and any Prop-sorted field, since an
invariant/proof field has no run-time representation. -/
def translateStructure (name : Name) : Meta.MetaM LStructureDefinition := do
  let env ← getEnv
  let ctor := Lean.getStructureCtor env name
  Meta.forallTelescope ctor.type fun xs _ => do
    let mut fields : List String := []
    for x in xs[ctor.numParams:] do
      let ld ← x.fvarId!.getDecl
      unless ← isErasableType ld.type do
        fields := fields ++ [toString ld.userName]
    pure { name := toString name, fields }

def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `LgtmLean }] {} (trustLevel := 1024)
  let names := env.constants.toList.filterMap fun (name, info) =>
    if isFunctionDecl info && isLgtmLeanDecl env name && !isCompilerGenerated env name then
      some name
    else
      none
  let sorted := names.map toString |>.mergeSort (· ≤ ·)
  let structNames := env.constants.toList.filterMap fun (name, info) =>
    if isStructureDecl env name info && isLgtmLeanDecl env name && !isCompilerGenerated env name then
      some name
    else
      none
  let sortedStructs := structNames.map toString |>.mergeSort (· ≤ ·)
  let coreCtx : Core.Context := { fileName := "extractor", fileMap := default }
  let coreState : Core.State := { env := env }
  let (_, _) ← ((do
      for nameStr in sortedStructs do
        let some name := (structNames.find? (toString · == nameStr)) | pure ()
        try
          let s ← translateStructure name
          IO.println (Std.Format.pretty (repr s))
        catch ex =>
          IO.println s!"-- failed to translate {name}: {(← ex.toMessageData.format).pretty}"
      for nameStr in sorted do
        let some name := (names.find? (toString · == nameStr)) | pure ()
        unless ← isPropReturningDecl name do
          try
            let f ← translateFunction name
            IO.println (Std.Format.pretty (repr f))
          catch ex =>
            IO.println s!"-- failed to translate {name}: {(← ex.toMessageData.format).pretty}"
      : Meta.MetaM Unit).run {} {}).toIO coreCtx coreState
