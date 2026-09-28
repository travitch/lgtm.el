module

public import LgtmDeepLean.Lang.IR
public import LgtmDeepLean.Lang.TypeCheck
public import LgtmDeepLean.Lang.Value
meta import LgtmDeepLean.Lang.IR
meta import LgtmDeepLean.Lang.TypeCheck
meta import LgtmDeepLean.Lang.Value
import LgtmDeepLean.Lang.Syntax

/-! # Evaluation

The relational semantics of the IR, and its soundness: evaluating a well-typed expression produces
a value of the type inferred for it.  Values, environments, and what it means for either to have a
type live in `Value.lean`. -/

/-- This is a relational evaluator for expressions under a given `Env` (environment).

This is the bridge from the deeply-embedded DSL to logical terms we can reason about
using standard Lean techniques.  The `Expression` is the DSL term while the `Value` is
how it would be evaluated in Lean.  Proofs are over the latter, which can use the full
Lean standard library.

`td` is carried only so that `EApp` can state `ArgsHaveType`: nothing here consults a type
declaration to compute anything.  A `structNew` is a name and the values its fields were given, a
`structGet` reads a field out of the value it finds, and a `structUpdate` rebinds the fields it names,
so evaluation needs no more of a struct than the value carries.  An `indNew` and an `indMatch` are
the same: the value carries the constructor it was built by, which is all the match needs to find its
alternative.  Whether that agrees with the declaration is the type checker's business, and
`Eval.hasType` is where the two meet. -/
public inductive Eval (td : TypeDecls) : Env → Expression → Value → Prop where
| ELam (ps : List (String × Ty)) (body : Expression) :
    Eval td env (.lam ps body) (env.closure ps body)
/-- A call evaluates its function and its arguments, then the body in the closure's environment
extended with the parameters. -/
| EApp (f : Expression) (args : List Expression) :
    Eval td env f (.closure cbindings cglobals ps body) →
    args.length = vs.length → (∀ p ∈ args.zip vs, Eval td env p.1 p.2) →
    ArgsHaveType td ps vs →
    Eval td (Env.extend ⟨cbindings, cglobals⟩ ps vs) body v →
    Eval td env (.app f args) v
| EBoolLit (b : Bool) : Eval td env (.boolLit b) (.bool b)
/-- A conditional whose condition came out `true` evaluates its first branch, and one whose condition
came out `false` its second.

Two rules rather than one over a `Bool`, so that a proof taking an `ite` apart is left with the branch
that ran rather than with an `if` to reduce, and so that the branch not taken is not mentioned at all:
it is never evaluated, which is the whole of what a conditional does that a two-argument function
could not.

A condition that evaluates to anything but a `bool` leaves this stuck — the only thing that can go
wrong here, and exactly what typing rules out. -/
| EIteTrue (c thn els : Expression) :
    Eval td env c (.bool true) → Eval td env thn v →
    Eval td env (.ite c thn els) v
| EIteFalse (c thn els : Expression) :
    Eval td env c (.bool false) → Eval td env els v →
    Eval td env (.ite c thn els) v
/-- Let binds a variable that shadows any existing bindings.

    The bound value is available in the body of the let.  This is a non-recursive let. -/
| ELet (x : String) (e : Expression) (body : Expression) :
    Eval td env e v₁ →
    Eval td ⟨(x, v₁) :: env.bindings, env.globals⟩ body v →
    Eval td env (.let_ x e body) v
| EVarRef (x : String) : env.lookup x = some v → Eval td env (.varRef x) v
/-- Building a struct evaluates each field's expression and keeps the result under that field's name.

The fields come out under the names they went in under and in the order they went in, which is what
`fes.map Prod.fst = fvs.map Prod.fst` says; the premise over the zip is then one evaluation per
field, the way `EApp`'s is one per argument.  Which names those are is not checked here — the
declaration is not consulted — so a `structNew` naming fields the struct does not have still
evaluates.  Being ill typed is what rules it out. -/
| EStructNew (name : String) (fes : List (FieldName × Expression)) :
    fes.map Prod.fst = fvs.map Prod.fst →
    (∀ p ∈ fes.zip fvs, Eval td env p.1.2 p.2.2) →
    Eval td env (.structNew name fes) (.struct name fvs)
/-- Reading a field evaluates the struct and hands back what that field is bound to.

Bound in the *value*, not declared in the struct: a field the value does not carry leaves this stuck,
which is the only thing that can go wrong here and is exactly what typing rules out. -/
| EStructGet (e : Expression) (f : FieldName) :
    Eval td env e (.struct name fvs) → fvs.lookup f = some v →
    Eval td env (.structGet e f) v
/-- Updating a struct evaluates it, evaluates each new field value, and rebinds those fields.

`FieldValues.update` rebinds in place, so the result carries the same fields in the same order as the
struct it came from and differs only in what the named ones hold.  Fields the update names that the
struct does not have are therefore dropped rather than added — again a case typing rules out. -/
| EStructUpdate (e : Expression) (fes : List (FieldName × Expression)) :
    Eval td env e (.struct name fvs) →
    fes.map Prod.fst = us.map Prod.fst →
    (∀ p ∈ fes.zip us, Eval td env p.1.2 p.2.2) →
    Eval td env (.structUpdate e fes) (.struct name (FieldValues.update fvs us))
/-- Applying a constructor evaluates one expression per data type it takes and keeps the values in
the order they were given, which is the order the constructor takes them in.

The premise is one evaluation per argument, the way `EStructNew`'s is one per field and `EApp`'s is
one per argument, with the lengths pinned down separately because `List.zip` stops at the shorter
list.  The two names are carried through as they were written: nothing here says the type has such a
constructor, or that it takes as many arguments as it was given.  Being ill typed is what rules those
out. -/
| EIndNew (name : String) (c : CtorName) (args : List Expression) :
    args.length = vs.length → (∀ p ∈ args.zip vs, Eval td env p.1 p.2) →
    Eval td env (.indNew name c args) (.ind name c vs)
/-- A match evaluates its scrutinee, takes the alternative for the constructor that built the value,
binds that alternative's names to the values the constructor carries, and evaluates its expression.

The alternative is found by name, so nothing here depends on where the declaration put a constructor
or on where the match put the alternative for it — which is how `Expression.inferAlts` reads them too,
resolving each alternative's constructor by name.  A match with no alternative for the value it was
handed is stuck, which is exactly what the exhaustiveness the type checker insists on rules out.

The names are bound the way a call binds its parameters — in front of the environment, so they shadow
it, and by `List.zip`, so a name repeated in one alternative takes the value of its leftmost
occurrence.  They are the alternative's own names: nothing about them survives into the value, which
is why the *type* of each has to come from the declaration when `Eval.hasType` types this. -/
| EIndMatch (scrut : Expression) (alts : List (CtorName × List String × Expression)) :
    Eval td env scrut (.ind name c vs) →
    alts.lookup c = some (xs, body) →
    Eval td ⟨xs.zip vs ++ env.bindings, env.globals⟩ body v →
    Eval td env (.indMatch scrut alts) v
| EIntLit (i : Int) : Eval td env (.intLit i) (.int i)
| EPlus (e₁ : Expression) (e₂ : Expression) : Eval td env e₁ (.int n₁) → Eval td env e₂ (.int n₂) → Eval td env (.plus e₁ e₂) (.int (n₁ + n₂))
| EMinus (e₁ : Expression) (e₂ : Expression) : Eval td env e₁ (.int n₁) → Eval td env e₂ (.int n₂) → Eval td env (.minus e₁ e₂) (.int (n₁ - n₂))
| EStringLit (s : String) : Eval td env (.stringLit s) (.string s)
| ENil (ty : Ty) : Eval td env (.lnil ty) (.list [])
| ECons (e₁ : Expression) (e₂ : Expression) : Eval td env e₁ v → Eval td env e₂ (.list vs) → Eval td env (.lcons e₁ e₂) (.list (v :: vs))
| EListReverse (e : Expression) : Eval td env e (.list vs) → Eval td env (.listReverse e) (.list vs.reverse)


/-- Evaluating a well-typed expression produces a value of its inferred type.

`ECons` needs no premise relating the new element to the rest of the list: `Expression.infer`
already requires the tail to be a list of the element type read off the head, so the values
`ECons` builds are homogeneous whenever the expression it evaluates is well typed.

`EVarRef` is the one rule that reads a value it did not build, so it is the one rule that needs
`henv`: the type inferred for a variable is the context's, and only `Env.HasType` ties that to the
value the environment hands back.  It is also the rule that resolves a global, and the two halves of
it line up because `Env.lookup` searches the bindings before the globals exactly as the context
`ctx ++ Globals.types env.globals` is searched left to right.

The two `ite` rules are the ones that say nothing at all about the value they produce: it is whatever
the branch that ran produced, so the induction hypothesis for that branch is the whole case.  It is
the type checker having held *both* branches to one type that makes this work, since which of them ran
is not something the type has heard about.

`ELet` is the other rule that extends the environment, and it is the easy one: the context grows on
the left exactly as the bindings do, so `Env.hasType_cons` — applied to the type the bound expression
was inferred at — is the whole case.

`EApp` is where the context stops being fixed, which is why the induction generalizes it: the
closure's body was checked against a context of its own, recovered from the closure's type, and has
nothing to do with the one the call was made in.  The argument-evaluation premise contributes
nothing here — `ArgsHaveType` already says what the argument values are, so the types the arguments
were *inferred* to have are only needed to line that up with the closure's parameters.

The three struct rules are where the argument-evaluation premise finally does the work `EApp`'s does
not.  A struct value carries no types, so nothing but the induction hypothesis says what its fields
hold: for each field, the expression that produced it is found by name and the type inference gave
that expression is the type its value has.  That the field names line up across the declaration, the
expressions and the values is what `Expression.map_fst_of_inferFields` and
`List.mem_zip_of_lookup` between them supply. -/
public theorem Eval.hasType {td : TypeDecls} {env : Env} {ctx : Context} {e : Expression}
    {v : Value} {t : Ty} (h : Eval td env e v) (henv : Env.HasType td env ctx)
    (ht : e.infer td (ctx ++ Globals.types env.globals) = some t) : v.HasType td t := by
  induction h generalizing ctx t with
  | @EVarRef v env x hx =>
      obtain ⟨hgs, hdom, hval⟩ := henv
      rw [Expression.infer_varRef, Context.lookup_append] at ht
      cases hb : env.bindings.lookup x with
      | some v' =>
          obtain ⟨t', hct⟩ := Option.isSome_iff_exists.mp (hdom x (by simp [hb]))
          obtain ⟨v'', hv'', hty⟩ := hval x t' hct
          rw [Env.lookup_of_bindings hb] at hx
          rw [hct] at ht
          grind
      | none =>
          have hcn : ctx.lookup x = none := by
            cases hc : ctx.lookup x with
            | none => rfl
            | some t' => obtain ⟨v', hv', -⟩ := hval x t' hc; simp [hv'] at hb
          rw [Env.lookup_of_globals hb] at hx
          rw [hcn, Globals.lookup_types] at ht
          obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp ht
          rw [hd, Option.map_some] at hx
          obtain rfl : v = Globals.value env.globals d := (Option.some.inj hx).symm
          refine Value.hasType_closure_iff.mpr ⟨[], d.resultType, ?_, ?_, ?_⟩
          · exact Globals.hasType_env hgs
          · simpa using FuncDecl.wellTyped_iff_infer_eq_some.mp (hgs x d hd)
          · simp [FuncDecl.ty]
  | ECons e₁ e₂ h₁ h₂ ih₁ ih₂ =>
      obtain ⟨t', ht₁, ht₂, rfl⟩ := Expression.infer_lcons_eq_some.mp ht
      have hv := ih₁ henv ht₁
      cases ih₂ henv ht₂ with
      | list hall => exact .list (by grind)
  | ELam ps body =>
      obtain ⟨r, hbody, rfl⟩ := Expression.infer_lam_eq_some.mp ht
      exact Value.hasType_closure_iff.mpr ⟨ctx, r, henv, by simpa using hbody, rfl⟩
  | EApp f args hf _ _ hat hbody ihf _ ihbody =>
      obtain ⟨ps', hfty, _⟩ := Expression.infer_app_eq_some.mp ht
      obtain ⟨cctx, r, hcenv, hbodyty, heq⟩ := Value.hasType_closure_iff.mp (ihf henv hfty)
      injection heq with _ hr
      refine ihbody (Env.hasType_extend hat hcenv) ?_
      simp only [Env.globals_extend]
      exact hr ▸ hbodyty
  | EIteTrue c thn els _ _ _ ihthn =>
      obtain ⟨-, hthn, -⟩ := Expression.infer_ite_eq_some.mp ht
      exact ihthn henv hthn
  | EIteFalse c thn els _ _ _ ihels =>
      obtain ⟨-, -, hels⟩ := Expression.infer_ite_eq_some.mp ht
      exact ihels henv hels
  | ELet x e body _ _ ih₁ ihbody =>
      obtain ⟨t', ht', htbody⟩ := Expression.infer_let_eq_some.mp ht
      exact ihbody (Env.hasType_cons (ih₁ henv ht') henv) htbody
  | EStructNew name fes hnames hev ihev =>
      obtain ⟨sd, hsd, hfts, rfl⟩ := Expression.infer_structNew_eq_some.mp ht
      have hkeys : sd.fields.map Prod.fst = fes.map Prod.fst :=
        Expression.map_fst_of_inferFields hfts
      refine .struct hsd (List.lookup_isSome_congr (hkeys.trans hnames)) fun f t' v' hft hfv => ?_
      obtain ⟨e, he⟩ : ∃ e, fes.lookup f = some e :=
        Option.isSome_iff_exists.mp (by rw [← List.lookup_isSome_congr hkeys f]; simp [hft])
      obtain ⟨t'', hft'', hinfer⟩ := Expression.lookup_of_inferFields hfts he
      obtain rfl : t'' = t' := by grind
      exact ihev _ (List.mem_zip_of_lookup hnames he hfv) henv hinfer
  | EStructGet e f _ hfv ihe =>
      obtain ⟨name', sd, he, hsd, hft⟩ := Expression.infer_structGet_eq_some.mp ht
      obtain ⟨sd', hsd', -, htys, hname⟩ := Value.hasType_struct_iff.mp (ihe henv he)
      simp only [Ty.struct.injEq] at hname
      subst hname
      obtain rfl : sd' = sd := by grind
      exact htys _ _ _ hft hfv
  | EStructUpdate e fes _ hnames hev ihe ihev =>
      obtain ⟨name', sd, fts, he, hsd, hfts, -, hfields, rfl⟩ :=
        Expression.infer_structUpdate_eq_some.mp ht
      obtain ⟨sd', hsd', hdom, htys, hname⟩ := Value.hasType_struct_iff.mp (ihe henv he)
      simp only [Ty.struct.injEq] at hname
      subst hname
      obtain rfl : sd' = sd := by grind
      refine .struct hsd (fun f => by simpa using hdom f)
        fun f t' v' hft hfv => FieldValues.hasType_update htys ?_ hft hfv
      -- What is left is the *new* values: each one is a field's expression evaluated, and the type
      -- checker has already said that expression has the type the declaration gives that field.
      intro f t' v' hft hus
      obtain ⟨e', he'⟩ : ∃ e', fes.lookup f = some e' :=
        Option.isSome_iff_exists.mp (by rw [List.lookup_isSome_congr hnames f]; simp [hus])
      obtain ⟨t'', hft'', hinfer⟩ := Expression.lookup_of_inferFields hfts he'
      obtain rfl : t'' = t' := by
        have := hfields (f, t'') (List.mem_of_lookup hft'')
        grind
      exact ihev _ (List.mem_zip_of_lookup hnames he' hus) henv hinfer
  | EIndNew name c args hlen hev ihev =>
      obtain ⟨d, ts, hd, hc, hts, rfl⟩ := Expression.infer_indNew_eq_some.mp ht
      obtain ⟨hvlen, hall⟩ :=
        Value.hasType_zip_of_inferList hlen hts fun p hp t' ht' => ihev p hp henv ht'
      exact .ind hd hc hvlen hall
  | EIndMatch scrut alts _ halt _ ihscrut ihbody =>
      obtain ⟨name', d, rs, hsc, hd, -, halts, -, hrs⟩ := Expression.infer_indMatch_eq_some.mp ht
      obtain ⟨d', ts, hd', hc, hvlen, hvals, hname⟩ := Value.hasType_ind_iff.mp (ihscrut henv hsc)
      simp only [Ty.ind.injEq] at hname
      subst hname
      obtain rfl : d' = d := by grind
      -- The alternative the value's constructor resolves to is the one checked against that
      -- constructor's data types, and every alternative was checked at the match's own type.
      obtain ⟨t', htmem, hxlen, hinfer⟩ := Expression.lookup_of_inferAlts halts hc halt
      obtain rfl : t' = t := hrs t' htmem
      exact ihbody (Env.hasType_match hxlen hvlen hvals henv) (by simpa using hinfer)
  | _ => grind [Value.HasType]

/-- `Apply d gs args v`: calling `d` with `args` among the globals `gs` returns `v`.

A call binds the parameters to the arguments positionally and evaluates the body under those
bindings over `gs`, so a body mentioning a name that is neither a parameter nor a global has no
value.

The `ArgsHaveType` premise is what makes a call with the wrong arguments stuck rather than junk:
arguments of the wrong type, or the wrong number of them, produce no value at all.  It is also
all `Apply.hasType` needs to read `d.parameters` as the context the body was checked in. -/
public inductive FuncDecl.Apply (d : FuncDecl) (td : TypeDecls) (gs : Globals) :
    List Value → Value → Prop where
| EApply (args : List Value) :
    ArgsHaveType td d.parameters args → Eval td (d.callEnv gs args) d.body v → Apply d td gs args v

/-- Calling a well-typed declaration among well-typed globals returns a value of its declared result
type.

Unlike `Eval.hasType` this needs no hypothesis about the local environment: `Apply` already requires
the arguments to match the parameters, and `Env.hasType_callEnv` turns that into the agreement
between environment and context that `Eval.hasType` asks for.  What is left is a property of the
declaration and the globals alone — nothing about this particular call. -/
public theorem FuncDecl.Apply.hasType {d : FuncDecl} {td : TypeDecls} {gs : Globals}
    {args : List Value} {v : Value} (h : d.Apply td gs args v) (hgs : Globals.WellTyped td gs)
    (hd : d.WellTyped td gs) : v.HasType td d.resultType := by
  cases h with
  | EApply _ hargs hbody =>
      exact hbody.hasType (Env.hasType_callEnv hgs hargs) (by simpa [FuncDecl.callEnv] using hd)

/-- Every declaration in a well-typed globals table is well typed, so a call to any of them returns
a value of the type it declares. -/
public theorem Globals.apply_hasType {td : TypeDecls} {gs : Globals} {x : String} {d : FuncDecl}
    {args : List Value} {v : Value} (hgs : Globals.WellTyped td gs) (hx : gs.lookup x = some d)
    (h : d.Apply td gs args v) : v.HasType td d.resultType :=
  h.hasType hgs (hgs x d hx)

/-- `p.Apply x args v`: calling the declaration `p` gives the name `x` with `args` returns `v`.

The body runs among `p`'s own globals and its own structure types, so it may call anything else `p`
declares — itself included — and mention any struct it declares.  A name `p` does not declare has no
call at all, which is the only way this differs from `FuncDecl.Apply` on `p.globals`. -/
public inductive Program.Apply (p : Program) (x : String) : List Value → Value → Prop where
| call (d : FuncDecl) :
    p.lookup x = some d → d.Apply p.typeDecls p.globals args v → Apply p x args v

/-- Calling a name in a well-typed program returns a value of the type the declaration under that
name declares.

This is the top of the stack: `Program.WellTyped` is a property of the program alone, checked once
by `Program.check`, and it covers every call to every name in it. -/
public theorem Program.Apply.hasType {p : Program} {x : String} {d : FuncDecl} {args : List Value}
    {v : Value} (h : p.Apply x args v) (hp : p.WellTyped) (hx : p.lookup x = some d) :
    v.HasType p.typeDecls d.resultType := by
  cases h with
  | call d' hx' hbody =>
      obtain rfl : d' = d := by grind
      exact Globals.apply_hasType hp hx' hbody

section Tests

/-- Add `x` to one less than `y`. -/
lgtm private def addPred as "add-pred" (x : int) (y : int) : int :=
  x + (y - 1)

-- This is a simple proof demonstrating how proofs work through the
-- relational evaluator
private theorem addPred.trivial_positive
  (x y res : Value)
  (hXPos : ∀ xv, .int xv = x → xv >= 1)
  (hYPos : ∀ yv, .int yv = y → yv >= 1)
  (hRes : FuncDecl.Apply addPred {} [] [ x, y ] res) :
  ∃ resv, res = .int resv ∧ resv > 0 := by
  obtain ⟨-, -, hbody⟩ := hRes
  cases hbody with
  | EPlus _ _ h₁ h₂ =>
    cases h₁ with
    | EVarRef _ hlx =>
      cases h₂ with
      | EMinus _ _ h₃ h₄ =>
        cases h₃ with
        | EVarRef _ hly =>
          cases h₄ with
          | EIntLit _ =>
            simp [addPred, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup, List.lookup]
              at hlx hly
            grind

-- A call evaluates its body under the arguments, read back out by `EVarRef`.
example : FuncDecl.Apply addPred {} [] [.int 2, .int 5] (.int 6) :=
  .EApply _ (.cons "x" (.int 2) (.cons "y" (.int 5) .nil))
    (.EPlus (n₁ := 2) (n₂ := 5 - 1) _ _ (.EVarRef "x" rfl)
      (.EMinus _ _ (.EVarRef "y" rfl) (.EIntLit 1)))

-- Whatever a call returns has the declared result type, and it is `addPred` being well typed that
-- says so, not anything about these particular arguments.
example (v : Value) (h : FuncDecl.Apply addPred {} [] [.int 2, .int 5] v) : v.HasType {} .int :=
  h.hasType Globals.wellTyped_nil (by simp [addPred, List.lookup])

-- A call with the wrong number of arguments is stuck, whether or not the body would have needed
-- the missing one.
example (v : Value) : ¬ FuncDecl.Apply addPred {} [] [.int 2] v := by
  rintro ⟨-, hargs, -⟩
  cases hargs with
  | cons _ _ hrest => cases hrest

example (v : Value) : ¬ FuncDecl.Apply addPred {} [] [.int 2, .int 5, .int 8] v := by
  rintro ⟨-, hargs, -⟩
  cases hargs with
  | cons _ _ hrest => cases hrest with | cons _ _ hrest => cases hrest

/-- Put `x` on the front of `xs`. -/
lgtm private def cons (x : int) (xs : list int) : list int :=
  x :: xs

/-- A one-element list is homogeneous for the reason its only element is. -/
private theorem hasType_singleton {v : Value} {t : Ty} (h : v.HasType td t) :
    Value.HasType td (.list [v]) (.list t) := .list (by simpa using h)

example : FuncDecl.Apply cons {} [] [.int 1, .list [.int 2]] (.list [.int 1, .int 2]) :=
  .EApply _ (.cons "x" (.int 1) (.cons "xs" (hasType_singleton (.int 2)) .nil))
    (.ECons _ _ (.EVarRef "x" rfl) (.EVarRef "xs" rfl))

-- An argument of the wrong type is now rejected at the call itself, rather than getting the body
-- stuck once it is looked up.
example (v : Value) : ¬ FuncDecl.Apply cons {} [] [.int 1, .int 2] v := by
  rintro ⟨-, hargs, -⟩
  cases hargs with
  | cons _ _ hrest => cases hrest with | cons _ hv _ => cases hv

/-- Reverse `xs` with `x` on the front. -/
lgtm private def revCons as "rev-cons" (x : int) (xs : list int) : list int :=
  reverse (x :: xs)

/-- A list of `int`s is homogeneous at `.list .int`, whatever its length. -/
private theorem hasType_intList {is : List Int} :
    Value.HasType td (.list (is.map .int)) (.list .int) :=
  .list (by simpa using fun i (_ : i ∈ is) => Value.HasType.int i)

-- `EListReverse` runs on the list `ECons` has just built, so the element pushed on the front comes
-- back last.
example : FuncDecl.Apply revCons {} [] [.int 1, .list [.int 2, .int 3]]
    (.list [.int 3, .int 2, .int 1]) :=
  .EApply _ (.cons "x" (.int 1) (.cons "xs" (hasType_intList (is := [2, 3])) .nil))
    (.EListReverse (vs := [.int 1, .int 2, .int 3]) _
      (.ECons _ _ (.EVarRef "x" rfl) (.EVarRef "xs" rfl)))

-- Reversing preserves the element type, so soundness gives the declared result type back with no
-- reasoning about this particular list.
example (v : Value) (h : FuncDecl.Apply revCons {} [] [.int 1, .list [.int 2, .int 3]] v) :
    v.HasType {} (.list .int) :=
  h.hasType Globals.wellTyped_nil (by simp [revCons, List.lookup])

-- Only a list can be reversed, so a body reversing one of the `int` parameters does not check.
example : ¬ ({ revCons with body := [lgtm| reverse x] } : FuncDecl).WellTyped {} [] := by
  simp [revCons, List.lookup]

/-- Reverse `xs` twice, which gives `xs` back. -/
lgtm private def reverseTwice as "reverse-twice" (xs : list int) : list int :=
  reverse (reverse xs)

/-- Reversing twice is the identity.

Inverting the two `EListReverse` steps down to the `EVarRef` that read `xs` leaves exactly
`List.reverse_reverse`, so this is a property of the program proved from the evaluator rather than
from any one input. -/
private theorem reverseTwice.eq_self {vs : List Value} {res : Value}
    (h : FuncDecl.Apply reverseTwice {} [] [.list vs] res) : res = .list vs := by
  obtain ⟨-, -, hbody⟩ := h
  cases hbody with
  | EListReverse _ h₁ =>
    cases h₁ with
    | EListReverse _ h₂ =>
      cases h₂ with
      | EVarRef _ hlx =>
        simp [reverseTwice, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup] at hlx
        grind

/-- The body of the inner lambda of `adderExpr`, `x + n`, which needs an `n` from outside itself. -/
private def adderInner : Expression := [lgtm| x + n]

/-- A function that builds a function.  Spliced together from `adderInner` rather than written out
so that the two are the same term, which the closures below are stated in terms of. -/
private def adderExpr : Expression := [lgtm| fun (n : int) => fun (x : int) => ~(adderInner)]

/-- The empty environment describes the empty context, which is all these examples need to say
about their environment. -/
private theorem hasType_nil : Env.HasType {} ∅ [] :=
  ⟨by simpa using Globals.wellTyped_nil, by simp, by simp⟩

-- Nothing in a lambda's body runs until it is applied; evaluating one only captures the
-- environment it was reached in.
example :
    Eval {} ∅ adderExpr ((∅ : Env).closure [("n", .int)] [lgtm| fun (x : int) => ~(adderInner)]) :=
  .ELam _ _

/-- Applying the outer lambda runs its body, which is itself a lambda, so what comes back is a
closure that has captured `n`. -/
private theorem eval_adder10 :
    Eval {} ∅ [lgtm| ~(adderExpr)(10)] (.closure [("n", .int 10)] [] [("x", .int)] adderInner) :=
  .EApp (vs := [.int 10]) _ _ (.ELam _ _) rfl
    (by rintro ⟨e, v⟩ hp; simp at hp; obtain ⟨rfl, rfl⟩ := hp; exact .EIntLit 10)
    (.cons "n" (.int 10) .nil) (.ELam _ _)

-- Applying that closure is what finally runs `x + n`, and it runs in the environment the closure
-- captured rather than the one the call was made from: `n` is in scope even though the caller's
-- environment is empty.
example : Eval {} ∅ [lgtm| ~(adderExpr)(10)(1)] (.int 11) :=
  .EApp (vs := [.int 1]) _ _ eval_adder10 rfl
    (by rintro ⟨e, v⟩ hp; simp at hp; obtain ⟨rfl, rfl⟩ := hp; exact .EIntLit 1)
    (.cons "x" (.int 1) .nil)
    (.EPlus (n₁ := 1) (n₂ := 10) _ _ (.EVarRef "x" rfl) (.EVarRef "n" rfl))

-- Soundness covers the new forms: a value of function type comes back, and which context the
-- closure captured is the theorem's business rather than the caller's.
example (v : Value) (h : Eval {} ∅ [lgtm| ~(adderExpr)(10)] v) : v.HasType {} (.fn [.int] .int) :=
  h.hasType hasType_nil (by simp [adderExpr, adderInner, List.lookup])

-- A call with the wrong number of arguments is stuck, just as it is for a declaration: the
-- parameters `ArgsHaveType` walks are the closure's own, so the lengths cannot disagree.
example (v : Value) : ¬ Eval {} ∅ [lgtm| ~(adderExpr)(1, 2)] v := by
  intro h
  cases h with
  | EApp f args hf hlen hargs hat hbody =>
      simp only [adderExpr] at hf
      cases hf
      cases hat with
      | cons _ _ hrest => cases hrest; simp at hlen

-- An argument of the wrong type is stuck too, so a closure cannot be entered with arguments its
-- parameters do not describe.
example (v : Value) : ¬ Eval {} ∅ [lgtm| ~(adderExpr)("a")] v := by
  intro h
  cases h with
  | EApp f args hf hlen hargs hat hbody =>
      simp only [adderExpr] at hf
      cases hf
      cases hat with
      | cons _ hv hrest =>
          cases hrest
          cases hargs _ (List.mem_cons_self ..)
          cases hv

/-! ## Let bindings

A `let_` is the one form that extends the environment without a call, so these are about what the
binding is and what it is not: it is in scope in the body, and it is not in scope in the expression
it binds. -/

-- A `let` binds the value its expression evaluated to, which `EVarRef` then reads out of the
-- bindings like any other name.
example : Eval {} ∅ [lgtm| let x = 1 + 2 in x + x] (.int 6) :=
  .ELet _ _ _ (.EPlus (n₁ := 1) (n₂ := 2) _ _ (.EIntLit 1) (.EIntLit 2))
    (.EPlus (n₁ := 3) (n₂ := 3) _ _ (.EVarRef "x" rfl) (.EVarRef "x" rfl))

-- Twice, so a later binding sees an earlier one.
example : Eval {} ∅ [lgtm| let x = 1 in let y = x + 1 in x + y] (.int 3) :=
  .ELet _ _ _ (.EIntLit 1)
    (.ELet _ _ _ (.EPlus (n₁ := 1) (n₂ := 1) _ _ (.EVarRef "x" rfl) (.EIntLit 1))
      (.EPlus (n₁ := 1) (n₂ := 2) _ _ (.EVarRef "x" rfl) (.EVarRef "y" rfl)))

/-- Twice one more than `n`. -/
lgtm private def letDouble as "let-double" (n : int) : int :=
  let m = n + 1 in m + m

#guard letDouble.check {} []

-- The binding goes in front of the call environment, so a `let` in a declaration's body sees the
-- parameters and the body sees the binding.
example : FuncDecl.Apply letDouble {} [] [.int 3] (.int 8) :=
  .EApply _ (.cons "n" (.int 3) .nil)
    (.ELet _ _ _ (.EPlus (n₁ := 3) (n₂ := 1) _ _ (.EVarRef "n" rfl) (.EIntLit 1))
      (.EPlus (n₁ := 4) (n₂ := 4) _ _ (.EVarRef "m" rfl) (.EVarRef "m" rfl)))

-- Soundness covers the new form: the declared result type comes back from `letDouble` checking,
-- with nothing said about the value the binding took.
example (v : Value) (h : FuncDecl.Apply letDouble {} [] [.int 3] v) : v.HasType {} .int :=
  h.hasType Globals.wellTyped_nil (by simp [letDouble, List.lookup])

/-- What a `let` binds is what its body computes with — here twice over, which is the property the
binding exists to express: `m` is evaluated once and read twice. -/
private theorem letDouble.eq_twice {n : Int} {res : Value}
    (h : FuncDecl.Apply letDouble {} [] [.int n] res) : res = .int (2 * (n + 1)) := by
  obtain ⟨-, -, hbody⟩ := h
  cases hbody with
  | ELet _ _ _ hm hbody =>
    cases hm with
    | EPlus _ _ h₁ h₂ =>
      cases h₁ with
      | EVarRef _ hln =>
        cases h₂ with
        | EIntLit _ =>
          cases hbody with
          | EPlus _ _ h₃ h₄ =>
            cases h₃ with
            | EVarRef _ hlm =>
              cases h₄ with
              | EVarRef _ hlm' =>
                simp [letDouble, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
                  List.lookup] at hln hlm hlm'
                grind

-- A `let` whose body is a lambda is how a closure captures something other than a parameter: the
-- same closure `~(adderExpr)(10)` returns, reached without a call.
example : Eval {} ∅ [lgtm| let n = 10 in fun (x : int) => ~(adderInner)]
    (.closure [("n", .int 10)] [] [("x", .int)] adderInner) :=
  .ELet _ _ _ (.EIntLit 10) (.ELam _ _)

-- The bound expression runs in the environment the `let` was reached in, so a `let` is not
-- recursive: `x` on the right of the `=` is the outer `x`, and with no outer `x` it is stuck.
example : Eval {} ∅ [lgtm| let x = 1 in let x = x + 1 in x] (.int 2) :=
  .ELet _ _ _ (.EIntLit 1)
    (.ELet _ _ _ (.EPlus (n₁ := 1) (n₂ := 1) _ _ (.EVarRef "x" rfl) (.EIntLit 1))
      (.EVarRef "x" rfl))

example (v : Value) : ¬ Eval {} ∅ [lgtm| let x = x + 1 in x] v := by
  intro h
  cases h with
  | ELet _ _ _ hx _ =>
      cases hx with
      | EPlus _ _ h₁ _ =>
          cases h₁ with
          | EVarRef _ hlx => simp [Env.lookup] at hlx

/-- Build a function that adds `n` to its argument. -/
lgtm private def adder (n : int) : (int) -> int :=
  fun (m : int) => n + m

-- A declaration can return a function, and `FuncDecl.Apply.hasType` covers that result type like
-- any other: what comes back is a closure, and the theorem says it is one of the declared type.
example (v : Value) (h : FuncDecl.Apply adder {} [] [.int 3] v) : v.HasType {} (.fn [.int] .int) :=
  h.hasType Globals.wellTyped_nil (by simp [adder, List.lookup])

/-! ## Booleans and conditionals

`EBoolLit` is where a `bool` comes from, and `ite` is what one is for: the one form that evaluates
only part of itself: `EIteTrue` and `EIteFalse` each mention one branch, and neither says anything
about the other.

A condition is therefore either a parameter or a literal.  The examples below use a parameter for the
properties that hold for every `b`, since that is what quantifying over the condition needs, and the
literals under them are the case where the branch that runs is settled by the expression alone. -/

-- A literal evaluates to the value it carries, the way `EIntLit` and `EStringLit` do.
example : Eval {} ∅ [lgtm| true] (.bool true) := .EBoolLit true
example : Eval {} ∅ [lgtm| false] (.bool false) := .EBoolLit false

-- And to nothing else, which is what makes a literal condition decide the branch outright.
example : ¬ Eval {} ∅ [lgtm| true] (.bool false) := by
  intro h; cases h

example : ¬ Eval {} ∅ [lgtm| true] (.int 1) := by
  intro h; cases h

/-- `x` when `b`, and `y` otherwise. -/
lgtm private def pick (b : bool) (x : int) (y : int) : int :=
  if b then { x } else { y }

#guard pick.check {} []

-- Which branch runs is decided by the condition, and it is `EIteTrue` or `EIteFalse` that says so.
example : FuncDecl.Apply pick {} [] [.bool true, .int 1, .int 2] (.int 1) :=
  .EApply _ (.cons "b" (.bool true) (.cons "x" (.int 1) (.cons "y" (.int 2) .nil)))
    (.EIteTrue _ _ _ (.EVarRef "b" rfl) (.EVarRef "x" rfl))

example : FuncDecl.Apply pick {} [] [.bool false, .int 1, .int 2] (.int 2) :=
  .EApply _ (.cons "b" (.bool false) (.cons "x" (.int 1) (.cons "y" (.int 2) .nil)))
    (.EIteFalse _ _ _ (.EVarRef "b" rfl) (.EVarRef "y" rfl))

-- Soundness covers the new form: the declared result type comes back from `pick` checking, with
-- nothing said about which branch ran — which is the reason both branches were held to one type.
example (v : Value) (b : Bool) (x y : Int)
    (h : FuncDecl.Apply pick {} [] [.bool b, .int x, .int y] v) : v.HasType {} .int :=
  h.hasType Globals.wellTyped_nil (by simp [pick, List.lookup])

-- A condition of any other type is stuck at the call, the way an argument of the wrong type is: a
-- `bool` is what `ite` asks for, and there is no truthiness to fall back on.
example (v : Value) : ¬ FuncDecl.Apply pick {} [] [.int 0, .int 1, .int 2] v := by
  rintro ⟨-, hargs, -⟩
  cases hargs with
  | cons _ hv _ => cases hv

/-- Which branch runs is decided by the condition and nothing else: this is the property a conditional
exists to express, for every `b` rather than for one.

Inverting it is two cases rather than one because there are two rules, and each leaves the branch that
ran — so `if b then x else y` on the Lean side is arrived at from the condition rather than assumed. -/
private theorem pick.eq_ite {b : Bool} {x y : Int} {res : Value}
    (h : FuncDecl.Apply pick {} [] [.bool b, .int x, .int y] res) :
    res = .int (if b then x else y) := by
  obtain ⟨-, -, hbody⟩ := h
  cases hbody with
  | EIteTrue _ _ _ hc hthn =>
    cases hc with
    | EVarRef _ hlb =>
      cases hthn with
      | EVarRef _ hlx =>
        simp [pick, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup, List.lookup] at hlb hlx
        grind
  | EIteFalse _ _ _ hc hels =>
    cases hc with
    | EVarRef _ hlb =>
      cases hels with
      | EVarRef _ hly =>
        simp [pick, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup, List.lookup] at hlb hly
        grind

-- The branch not taken is never evaluated, which is the whole of what a conditional does that a
-- two-argument function could not: the `else` below has no value at all, and the call still has one.
#guard !({ pick with body := [lgtm| if b then { x } else { missing() }] } : FuncDecl).check {} []

example : FuncDecl.Apply { pick with body := [lgtm| if b then { x } else { missing() }] } {} []
    [.bool true, .int 1, .int 2] (.int 1) :=
  .EApply _ (.cons "b" (.bool true) (.cons "x" (.int 1) (.cons "y" (.int 2) .nil)))
    (.EIteTrue _ _ _ (.EVarRef "b" rfl) (.EVarRef "x" rfl))

/-- `xs` reversed when `b`, and as it came otherwise.  The branches are `list`s rather than `int`s,
which is what the form being polymorphic comes to: a conditional produces whatever they produce. -/
lgtm private def maybeReverse as "maybe-reverse" (b : bool) (xs : list int) : list int :=
  if b then { reverse xs } else { xs }

#guard maybeReverse.check {} []

example : FuncDecl.Apply maybeReverse {} [] [.bool true, .list [.int 1, .int 2]]
    (.list [.int 2, .int 1]) :=
  .EApply _ (.cons "b" (.bool true) (.cons "xs" (hasType_intList (is := [1, 2])) .nil))
    (.EIteTrue _ _ _ (.EVarRef "b" rfl)
      (.EListReverse (vs := [.int 1, .int 2]) _ (.EVarRef "xs" rfl)))

example : FuncDecl.Apply maybeReverse {} [] [.bool false, .list [.int 1, .int 2]]
    (.list [.int 1, .int 2]) :=
  .EApply _ (.cons "b" (.bool false) (.cons "xs" (hasType_intList (is := [1, 2])) .nil))
    (.EIteFalse _ _ _ (.EVarRef "b" rfl) (.EVarRef "xs" rfl))

example (v : Value) (b : Bool) (vs : List Value)
    (h : FuncDecl.Apply maybeReverse {} [] [.bool b, .list vs] v) : v.HasType {} (.list .int) :=
  h.hasType Globals.wellTyped_nil (by simp [maybeReverse, List.lookup])

/-- `x` when the condition is spelled out, which is `pick` with its own condition: a declaration of no
`bool` parameter that still runs a conditional. -/
lgtm private def pickFirst as "pick-first" (x : int) (y : int) : int :=
  if true then { x } else { y }

#guard pickFirst.check {} []

example : FuncDecl.Apply pickFirst {} [] [.int 1, .int 2] (.int 1) :=
  .EApply _ (.cons "x" (.int 1) (.cons "y" (.int 2) .nil))
    (.EIteTrue _ _ _ (.EBoolLit true) (.EVarRef "x" rfl))

-- Which branch runs is now settled by the body rather than by the caller, so this holds for every
-- pair of arguments and mentions only the one that comes back: `EIteFalse` would need the literal to
-- have evaluated to `false`, and `EBoolLit` gives only `true`.
private theorem pickFirst.eq_fst {x y : Int} {res : Value}
    (h : FuncDecl.Apply pickFirst {} [] [.int x, .int y] res) : res = .int x := by
  obtain ⟨-, -, hbody⟩ := h
  cases hbody with
  | EIteTrue _ _ _ _ hthn =>
    cases hthn with
    | EVarRef _ hlx =>
      simp [pickFirst, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup] at hlx
      grind
  | EIteFalse _ _ _ hc _ => cases hc

example (v : Value) (x y : Int) (h : FuncDecl.Apply pickFirst {} [] [.int x, .int y] v) :
    v.HasType {} .int :=
  h.hasType Globals.wellTyped_nil (by simp [pickFirst, List.lookup])

/-- The literal on its own, which is the shortest declaration that returns a `bool`. -/
lgtm private def yes : bool := true

#guard yes.check {} []

example : FuncDecl.Apply yes {} [] [] (.bool true) := .EApply _ .nil (.EBoolLit true)

-- Soundness covers the new form: the declared result type comes back from `yes` checking, which is
-- `Value.HasType.bool` reached through the catch-all case of `Eval.hasType` the other literals use.
example (v : Value) (h : FuncDecl.Apply yes {} [] [] v) : v.HasType {} .bool :=
  h.hasType Globals.wellTyped_nil (by simp [yes])

/-! ## Globals

Everything above ran with an empty table, so every name a body mentioned was one of its own
parameters.  These declare a table and call across it. -/

/-- Twice `n`. -/
lgtm private def double (n : int) : int :=
  n + n

/-- Four times `n`, which is `double` calling `double`. -/
lgtm private def quad (n : int) : int :=
  double(double(n))

/-- One more than twice `n`. -/
lgtm private def doublePlus as "double-plus" (n : int) : int :=
  double(n) + 1

/-- The answer.  A declaration of no parameters is how a global *variable* is written: its name has
type `() -> int`, so reading it is the call `answer()`. -/
lgtm private def answer : int :=
  42

/-- One more than the answer, which is where the nullary global gets read. -/
lgtm private def answerPlus as "answer-plus" : int :=
  answer() + 1

private def arith : Globals := Globals.ofDecls [double, quad, doublePlus, answer, answerPlus]

-- A body may mention a global, and `FuncDecl.check` finds it at the type its declaration gives.
#guard quad.check {} arith
#guard answerPlus.check {} arith
#guard Globals.check {} arith

-- Without the table the same name is free, and the body does not check.  This is all `Globals` adds
-- to the checker: `double` has a type in `quad`'s body only because `arith` says so.
#guard !quad.check {} []
#guard !answerPlus.check {} []

-- The arity is the declaration's, so a global is as picky about how many arguments it gets as any
-- other function, and a nullary global has to be called rather than just named.
#guard !({ quad with body := [lgtm| double(1, 2)] } : FuncDecl).check {} arith
#guard !({ answerPlus with body := [lgtm| answer + 1] } : FuncDecl).check {} arith

-- A parameter shadows a global of the same name, in the checker and in `Env.lookup` alike.
#guard ({ quad with parameters := [("double", .int)], body := [lgtm| double] }
  : FuncDecl).check {} arith
#guard !({ quad with parameters := [("double", .int)], body := [lgtm| double(1)] }
  : FuncDecl).check {} arith

-- A `let` shadows a global the same way a parameter does, so the name becomes a value rather than
-- something to call.
#guard ({ quad with body := [lgtm| let double = n in double] } : FuncDecl).check {} arith
#guard !({ quad with body := [lgtm| let double = n in double(1)] } : FuncDecl).check {} arith

-- And `Env.lookup` reads it the same way round: the binding is found before the globals are
-- consulted, so the closure `double` would have resolved to is never built.
example : FuncDecl.Apply { quad with body := [lgtm| let double = n in double] } {} arith [.int 3]
    (.int 3) :=
  .EApply _ (.cons "n" (.int 3) .nil) (.ELet _ _ _ (.EVarRef "n" rfl) (.EVarRef "double" rfl))

-- A name that is neither a parameter nor a global is still free.
#guard !({ double with body := [lgtm| missing(n)] } : FuncDecl).check {} arith

/-- Every declaration in `arith` checks, which is what a call to any of them needs. -/
private theorem arith.wellTyped : Globals.WellTyped {} arith := by
  refine Globals.wellTyped_of_forall fun p hp => ?_
  simp only [arith, Globals.ofDecls, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    simp [double, quad, doublePlus, answer, answerPlus, arith, Globals.ofDecls,
      FuncDecl.ty, List.lookup]

/-- A call across the table: `double` is not bound in `doublePlus`'s call environment, so
`Env.lookup` falls through to the globals and builds its closure there.

The body then runs in *that* closure's environment — `double`'s own parameter over the same globals
— and not in the one the call was made from. -/
private theorem eval_doublePlus : FuncDecl.Apply doublePlus {} arith [.int 3] (.int 7) :=
  .EApply _ (.cons "n" (.int 3) .nil)
    (.EPlus (n₁ := 6) (n₂ := 1) _ _
      (.EApp (vs := [.int 3]) _ _ (.EVarRef "double" rfl) rfl
        (by rintro ⟨e, v⟩ hp; simp at hp; obtain ⟨rfl, rfl⟩ := hp; exact .EVarRef "n" rfl)
        (.cons "n" (.int 3) .nil)
        (.EPlus (n₁ := 3) (n₂ := 3) _ _ (.EVarRef "n" rfl) (.EVarRef "n" rfl)))
      (.EIntLit 1))

-- Soundness covers a call that goes through the table, and the reason is that every declaration in
-- `arith` checks — nothing about this particular call.
example (v : Value) (h : FuncDecl.Apply doublePlus {} arith [.int 3] v) : v.HasType {} .int :=
  h.hasType arith.wellTyped (arith.wellTyped "double-plus" doublePlus rfl)

-- `Globals.apply_hasType` is that statement read off the table, for whichever entry a name resolves
-- to, so the caller needs no `FuncDecl.WellTyped` of its own.
example (v : Value) (h : FuncDecl.Apply answerPlus {} arith [] v) : v.HasType {} .int :=
  Globals.apply_hasType (x := "answer-plus") arith.wellTyped rfl h

/-- Recursion is what a table of declarations buys over a table of values: `countdown` is checked in
a context that already holds `countdown`, so it may call itself. -/
lgtm private def countdown (n : int) : int :=
  countdown(n - 1)

#guard Globals.check {} (Globals.ofDecls [countdown])
#guard !countdown.check {} []

/-- Mutual recursion needs nothing further: both are in the context both are checked against. -/
lgtm private def ping (n : int) : int :=
  pong(n - 1)

lgtm private def pong (n : int) : int :=
  ping(n - 1)

#guard Globals.check {} (Globals.ofDecls [ping, pong])

-- Neither checks alone, and neither checks with only itself in scope: it is the table that ties
-- them together.
#guard !ping.check {} []
#guard !ping.check {} (Globals.ofDecls [ping])
#guard !Globals.check {} (Globals.ofDecls [ping])

/-! ## Programs

The same declarations again, read as a source file rather than as a table: `arith` is what
`arithProgram` presents to its own bodies. -/

private def arithProgram : Program :=
  { funcDecls := [double, quad, doublePlus, answer, answerPlus] }

example : arithProgram.globals = arith := rfl

#guard arithProgram.check

-- A program resolves the names its declarations declare, so `as` is what shows up here and the Lean
-- name does not.
example : arithProgram.lookup "double-plus" = some doublePlus := rfl
example : arithProgram.lookup "doublePlus" = none := rfl
example : arithProgram.lookup "missing" = none := rfl

-- No two of them share a name, so none is shadowed and every one can be called.
example : arithProgram.NamesUnique := by decide
example : ¬ ({ funcDecls := [double, double] } : Program).NamesUnique := by decide

-- Which is what `lookup_self` is for: being one of the program's declarations is enough.
example : arithProgram.lookup quad.name = some quad :=
  arithProgram.lookup_self (by decide) (by simp [arithProgram])

-- A duplicate name is not unsound, just dead: the second declaration is checked and unreachable.
#guard ({ funcDecls := [double, { double with resultType := .int }] } : Program).check
example : ({ funcDecls := [answer, { answer with resultType := .string }] }
    : Program).lookup "answer" = some answer := rfl

/-- `arithProgram` checks, which is a property of the program alone. -/
private theorem arithProgram.wellTyped : arithProgram.WellTyped := arith.wellTyped

-- Running a program is calling one of its names, and the body runs among the program's own
-- declarations.
example : arithProgram.Apply "double-plus" [.int 3] (.int 7) :=
  .call _ rfl eval_doublePlus

-- Soundness at the top: one hypothesis about the whole program covers every call to every name in
-- it, whatever the arguments.
example (v : Value) (h : arithProgram.Apply "double-plus" [.int 3] v) : v.HasType {} .int :=
  h.hasType arithProgram.wellTyped rfl

example (v : Value) (args : List Value) (h : arithProgram.Apply "answer-plus" args v) :
    v.HasType {} .int :=
  h.hasType arithProgram.wellTyped rfl

-- A name the program does not declare has no call at all.
example (v : Value) : ¬ arithProgram.Apply "missing" [.int 3] v := by
  rintro ⟨d, hd, -⟩
  rw [show arithProgram.lookup "missing" = none from rfl] at hd
  simp at hd

/-! ## Structs

A structure type is a top-level entity, so these examples carry a table of them the way the ones
above carry a table of declarations.  Evaluation never consults that table — the three struct rules
work on the value alone — so it shows up only where a type does: in `check`, in `Value.HasType`, and
in `ArgsHaveType`, which is why `Eval` carries it at all. -/

/-- A point in the plane. -/
lgtm private struct Point { x : int, y : int }

private def points : TypeDecls := { ss := Structs.ofDecls [Point] }

/-- A `Point` value has the type `Point` declares exactly when both its coordinates are `int`s.

Every `Value.HasType` for a struct comes down to a case analysis on the field name like this one: the
declaration and the value agree on which fields there are, and on each field they agree on the type.
Nothing here is about these particular coordinates, which is why one lemma covers every `Point`. -/
private theorem hasType_point {a b : Int} :
    Value.HasType points (.struct "Point" [("x", .int a), ("y", .int b)]) (.struct "Point") :=
  Value.hasType_struct_of_fields rfl rfl (by
    rintro p hp
    simp [Point] at hp
    rcases hp with rfl | rfl <;> exact .int _)

/-- Swap `p`'s coordinates. -/
lgtm private def swap (p : struct Point) : struct Point :=
  new Point { x = p.y, y = p.x }

#guard swap.check points []

-- Without the struct table the body does not check: `new Point { … }` has nothing to check its
-- fields against, and the result type names nothing.  This is all `Structs` adds to the checker, and
-- it is the same thing `Globals` adds for names.
#guard !swap.check {} []

/-- `EStructNew` evaluates one expression per field and keeps each result under that field's name, so
building a struct out of another one's fields is two `EStructGet`s under an `EStructNew`.

The globals are left open because nothing in this call reads one: `p` is a parameter, so `Env.lookup`
finds it in the bindings and never reaches the table. -/
private theorem eval_swap {gs : Globals} : FuncDecl.Apply swap points gs
    [.struct "Point" [("x", .int 1), ("y", .int 2)]]
    (.struct "Point" [("x", .int 2), ("y", .int 1)]) :=
  .EApply _ (.cons "p" hasType_point .nil)
    (.EStructNew _ _ rfl (by
      rintro p hp
      simp at hp
      rcases hp with rfl | rfl <;> exact .EStructGet _ _ (.EVarRef "p" rfl) rfl))

-- Soundness covers the new forms: what comes back has the declared struct type, and the reason is
-- that `swap` checks against `points` — nothing about this particular point.
example (v : Value)
    (h : FuncDecl.Apply swap points [] [.struct "Point" [("x", .int 1), ("y", .int 2)]] v) :
    v.HasType points (.struct "Point") :=
  h.hasType Globals.wellTyped_nil (by simp [swap, Point, points, List.lookup])

/-- One more than `p`'s `x`, which is the field read on its own. -/
lgtm private def getX as "get-x" (p : struct Point) : int :=
  p.x + 1

#guard getX.check points []

-- `EStructGet` reads the field out of the value, so it is the `EVarRef` that found the struct that
-- decides what comes back.
example : FuncDecl.Apply getX points [] [.struct "Point" [("x", .int 1), ("y", .int 2)]] (.int 2) :=
  .EApply _ (.cons "p" hasType_point .nil)
    (.EPlus (n₁ := 1) (n₂ := 1) _ _ (.EStructGet _ _ (.EVarRef "p" rfl) rfl) (.EIntLit 1))

-- A field the declaration does not list is not a field, so a body reading one does not check even
-- though the value it would be handed at run time carries only declared fields.
#guard !({ getX with body := [lgtm| p.z + 1] } : FuncDecl).check points []

/-- Reading a field gives what the value has bound to it, which is the property `structGet` exists to
express: the point's other fields, and whatever else it carries, do not come into it. -/
private theorem getX.eq_succ_x {fvs : FieldValues} {a : Int} {res : Value}
    (hx : fvs.lookup "x" = some (.int a))
    (h : FuncDecl.Apply getX points [] [.struct "Point" fvs] res) : res = .int (a + 1) := by
  obtain ⟨-, -, hbody⟩ := h
  cases hbody with
  | EPlus _ _ h₁ h₂ =>
    cases h₁ with
    | EStructGet _ _ hp hfx =>
      cases hp with
      | EVarRef _ hlp =>
        cases h₂ with
        | EIntLit _ =>
          simp [getX, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup] at hlp
          obtain ⟨rfl, rfl⟩ := hlp
          grind

/-- Move `p` along the x axis. -/
lgtm private def shiftX as "shift-x" (p : struct Point) (d : int) : struct Point :=
  { p with x = p.x + d }

#guard shiftX.check points []

-- An update rebinds the fields it names in place, so `y` comes through untouched and the fields stay
-- in the order `Point` declares them.
example : FuncDecl.Apply shiftX points [] [.struct "Point" [("x", .int 1), ("y", .int 2)], .int 10]
    (.struct "Point" [("x", .int 11), ("y", .int 2)]) := by
  refine .EApply _ (.cons "p" hasType_point (.cons "d" (.int 10) .nil)) ?_
  -- Both field lists have to be given: the result is `FieldValues.update fvs us`, and unification
  -- cannot read either of them back out of the value that comes out.
  refine .EStructUpdate (fvs := [("x", .int 1), ("y", .int 2)]) (us := [("x", .int 11)])
    (.varRef "p") [("x", .plus (.structGet (.varRef "p") "x") (.varRef "d"))] ?_ rfl ?_
  · exact .EVarRef "p" rfl
  · rintro p hp
    simp at hp
    subst hp
    exact .EPlus (n₁ := 1) (n₂ := 10) _ _ (.EStructGet _ _ (.EVarRef "p" rfl) rfl)
      (.EVarRef "d" rfl)

-- An empty update is rejected, as `Expression.structUpdate` says it must be: it would be the
-- expression it updates, written so as to suggest otherwise.
#guard !({ shiftX with body := [lgtm| { p with }] } : FuncDecl).check points []

-- And a field the declaration does not have cannot be introduced by one.
#guard !({ shiftX with body := [lgtm| { p with z = d }] } : FuncDecl).check points []

/-- What an update leaves alone is the property it exists to express: `shift-x` moves `x` by `d` and
hands `y` back as it found it, for every point and every distance.

The update names one field, so `y` is a field it does not name — and `List.lookup_isSome_congr`,
applied to the premise that the expressions and the values share their field names, is what says an
update cannot reach a field it did not mention. -/
private theorem shiftX.eq_shifted {fvs : FieldValues} {a b d : Int} {res : Value}
    (hx : fvs.lookup "x" = some (.int a)) (hy : fvs.lookup "y" = some (.int b))
    (h : FuncDecl.Apply shiftX points [] [.struct "Point" fvs, .int d] res) :
    ∃ fvs', res = .struct "Point" fvs'
      ∧ fvs'.lookup "x" = some (.int (a + d)) ∧ fvs'.lookup "y" = some (.int b) := by
  obtain ⟨-, -, hbody⟩ := h
  cases hbody with
  | @EStructUpdate _ _ _ us _ _ hp hnames hev =>
    cases hp with
    | EVarRef _ hlp =>
      simp [shiftX, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup] at hlp
      obtain ⟨rfl, rfl⟩ := hlp
      refine ⟨_, rfl, ?_, ?_⟩
      · -- The one field the update names is `x`, and what it was given there is `p.x + d`.
        obtain ⟨w, hw⟩ : ∃ w, us.lookup "x" = some w :=
          Option.isSome_iff_exists.mp (by rw [← List.lookup_isSome_congr hnames "x"]; simp)
        have hev' := hev _ (List.mem_zip_of_lookup hnames
          (b := .plus (.structGet (.varRef "p") "x") (.varRef "d")) (by simp) hw)
        cases hev' with
        | EPlus _ _ h₁ h₂ =>
          cases h₁ with
          | EStructGet _ _ hq hfx =>
            cases hq with
            | EVarRef _ hlq =>
              cases h₂ with
              | EVarRef _ hld =>
                simp [shiftX, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
                  List.lookup] at hlq hld
                rw [FieldValues.lookup_update, hx, hw]
                grind
      · -- And `y` it does not name at all, so `FieldValues.update` passes it straight through.
        have : us.lookup "y" = none := by
          rw [← Option.not_isSome_iff_eq_none, ← List.lookup_isSome_congr hnames "y"]
          simp
        rw [FieldValues.lookup_update, hy, this]
        rfl

/-! ### A program with structs

The same declarations again, read as a source file: a `Program` carries its structure types beside
its declarations, and `Program.typeDecls` is the bundle its bodies are checked and run against. -/

private def pointProgram : Program where
  funcDecls := [swap, getX, shiftX]
  structDecls := [Point]

example : pointProgram.typeDecls = points := rfl

#guard pointProgram.check

-- The struct declaration is what makes it check: without it the three bodies mention a type that
-- names nothing.
#guard !({ pointProgram with structDecls := [] } : Program).check

-- A program resolves the struct names it declares, and no two of them share a name — the counterpart
-- of `NamesUnique` for types rather than for declarations.
example : pointProgram.lookupStruct "Point" = some Point := rfl
example : pointProgram.lookupStruct "Pair" = none := rfl
example : pointProgram.StructNamesUnique := by decide
example : ¬ ({ pointProgram with structDecls := [Point, Point] } : Program).StructNamesUnique := by
  decide

-- Which is what `lookupStruct_self` is for: being one of the program's structure declarations is
-- enough to be the one its own name resolves to.
example : pointProgram.lookupStruct Point.name = some Point :=
  pointProgram.lookupStruct_self (by decide) (by simp [pointProgram])

-- No declaration of it names a field twice either, and this one `check` is about: the extra
-- declaration below is one no body mentions, so the three bodies check exactly as before and it is
-- the repeated field alone that turns the program down.
example : pointProgram.FieldNamesUnique := by decide
#guard !({ pointProgram with
  structDecls := [Point, { name := "Dup", fields := [("x", .int), ("x", .string)] }] }
  : Program).check
#guard ({ pointProgram with structDecls := [Point, { name := "Dup", fields := [("x", .int)] }] }
  : Program).check

/-- `pointProgram` checks, which is a property of the program alone. -/
private theorem pointProgram.wellTyped : pointProgram.WellTyped := by
  refine Globals.wellTyped_of_forall fun p hp => ?_
  simp only [Program.globals, pointProgram, Globals.ofDecls, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    simp [swap, getX, shiftX, Point, Program.globals, Program.typeDecls, Program.structs,
      pointProgram, Globals.ofDecls, Structs.ofDecls, FuncDecl.ty, List.lookup]

-- Running it is calling one of its names, and soundness at the top covers a struct result type like
-- any other.
example : pointProgram.Apply "swap" [.struct "Point" [("x", .int 1), ("y", .int 2)]]
    (.struct "Point" [("x", .int 2), ("y", .int 1)]) :=
  .call _ rfl eval_swap

example (v : Value)
    (h : pointProgram.Apply "swap" [.struct "Point" [("x", .int 1), ("y", .int 2)]] v) :
    v.HasType pointProgram.typeDecls (.struct "Point") :=
  h.hasType pointProgram.wellTyped rfl

example (v : Value) (args : List Value) (h : pointProgram.Apply "get-x" args v) :
    v.HasType pointProgram.typeDecls .int :=
  h.hasType pointProgram.wellTyped rfl

/-! ## Inductive types

An inductive type is a top-level entity the way a structure type is, so these carry a table of them
the same way.  Evaluation does not consult that table either: `EIndNew` keeps the two names it was
given, and `EIndMatch` finds its alternative by the constructor the value it took apart carries. -/

/-- A colour, which is what an inductive type carrying nothing anywhere comes to. -/
lgtm private inductive Color { Red, Green, Blue }

/-- A shape, whose constructors carry what it takes to measure one. -/
lgtm private inductive Shape { Circle(int), Rect(int, int) }

private def shapes : TypeDecls := { is := Inductives.ofDecls [Color, Shape] }

/-- A `Rect` has the type `Shape` declares exactly when both its sides are `int`s.

Every `Value.HasType` for an inductive value comes down to a walk along the zip like this one: the
constructor is looked up in the declaration, and what it carries is held to the types found there,
one for one.  Nothing here is about these particular sides, which is why one lemma covers every
`Rect`. -/
private theorem hasType_rect {w h : Int} :
    Value.HasType shapes (.ind "Shape" "Rect" [.int w, .int h]) (.ind "Shape") :=
  .ind rfl rfl rfl (by rintro p hp; simp at hp; rcases hp with rfl | rfl <;> exact .int _)

/-- A constructor carrying nothing has nothing to hold to a type, so the walk is empty. -/
private theorem hasType_red : Value.HasType shapes (.ind "Color" "Red" []) (.ind "Color") :=
  .ind rfl rfl rfl (by simp)

/-- How big `s` is, for a rough enough notion of size. -/
lgtm private def area (s : inductive Shape) : int :=
  match s with | Circle(r) => r + r | Rect(w, h) => w + h

#guard area.check shapes []

-- Without the inductive table the body does not check: the alternatives have no constructors to be
-- exhaustive over, and the parameter's type names nothing.  This is all `Inductives` adds to the
-- checker, and it is the same thing `Structs` adds for the other kind of type.
#guard !area.check {} []

/-- The same function with its alternatives the other way round from the declaration's constructors.

An alternative says which constructor it is for, so this is the same function as `area`: it checks,
and `EIndMatch` finds the alternative for the value's constructor wherever in the match it was
written. -/
lgtm private def areaSwapped as "area-swapped" (s : inductive Shape) : int :=
  match s with | Rect(w, h) => w + h | Circle(r) => r + r

#guard areaSwapped.check shapes []

example : FuncDecl.Apply areaSwapped shapes [] [.ind "Shape" "Rect" [.int 3, .int 4]] (.int 7) :=
  .EApply _ (.cons "s" hasType_rect .nil)
    (.EIndMatch _ _ (.EVarRef "s" rfl) rfl
      (.EPlus (n₁ := 3) (n₂ := 4) _ _ (.EVarRef "w" rfl) (.EVarRef "h" rfl)))

example : FuncDecl.Apply areaSwapped shapes [] [.ind "Shape" "Circle" [.int 5]] (.int 10) :=
  .EApply _ (.cons "s" (.ind rfl rfl rfl (by rintro p hp; simp at hp; subst hp; exact .int _)) .nil)
    (.EIndMatch _ _ (.EVarRef "s" rfl) rfl
      (.EPlus (n₁ := 5) (n₂ := 5) _ _ (.EVarRef "r" rfl) (.EVarRef "r" rfl)))

-- Reordering is all the alternatives are free to do: a constructor left out is still not exhaustive,
-- and neither is one named twice in place of the one that is missing.
#guard !({ areaSwapped with body := [lgtm| match s with | Rect(w, h) => w + h] }
  : FuncDecl).check shapes []
#guard !({ areaSwapped with
  body := [lgtm| match s with | Rect(w, h) => w + h | Rect(w, h) => w] } : FuncDecl).check shapes []

/-- `EIndMatch` takes the alternative for the constructor the value carries and binds that
alternative's names to what the constructor holds, so a call comes down to the arithmetic in one
alternative and nothing at all in the others. -/
private theorem eval_area {gs : Globals} : FuncDecl.Apply area shapes gs
    [.ind "Shape" "Rect" [.int 3, .int 4]] (.int 7) :=
  .EApply _ (.cons "s" hasType_rect .nil)
    (.EIndMatch _ _ (.EVarRef "s" rfl) rfl
      (.EPlus (n₁ := 3) (n₂ := 4) _ _ (.EVarRef "w" rfl) (.EVarRef "h" rfl)))

-- The other alternative is chosen by the other constructor, and the names it binds are its own.
example : FuncDecl.Apply area shapes [] [.ind "Shape" "Circle" [.int 5]] (.int 10) :=
  .EApply _ (.cons "s" (.ind rfl rfl rfl (by rintro p hp; simp at hp; subst hp; exact .int _)) .nil)
    (.EIndMatch _ _ (.EVarRef "s" rfl) rfl
      (.EPlus (n₁ := 5) (n₂ := 5) _ _ (.EVarRef "r" rfl) (.EVarRef "r" rfl)))

-- Soundness covers the new forms: what comes back has the declared type, and the reason is that
-- `area` checks against `shapes` — nothing about this particular shape.
example (v : Value) (h : FuncDecl.Apply area shapes [] [.ind "Shape" "Rect" [.int 3, .int 4]] v) :
    v.HasType shapes .int :=
  h.hasType Globals.wellTyped_nil
    (by simp [area, Color, Shape, shapes, List.lookup, Expression.altsExhaustive, List.isPerm])

/-- Which alternative runs is decided by the constructor and nothing else, and what it computes with
is what that constructor carries: this is the property a match exists to express, for every `Rect`
rather than for one. -/
private theorem area.rect {w h : Int} {res : Value}
    (hres : FuncDecl.Apply area shapes [] [.ind "Shape" "Rect" [.int w, .int h]] res) :
    res = .int (w + h) := by
  obtain ⟨-, -, hbody⟩ := hres
  cases hbody with
  | EIndMatch _ _ hs halt hb =>
    cases hs with
    | EVarRef _ hls =>
      simp [area, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup] at hls
      obtain ⟨rfl, rfl, rfl⟩ := hls
      simp [List.lookup] at halt
      obtain ⟨rfl, rfl⟩ := halt
      cases hb with
      | EPlus _ _ h₁ h₂ =>
        cases h₁ with
        | EVarRef _ hlw =>
          cases h₂ with
          | EVarRef _ hlh =>
            simp [area, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
              List.lookup] at hlw hlh
            grind

/-- A square of side `n`, which is the other half: a constructor applied to values. -/
lgtm private def square (n : int) : inductive Shape :=
  new Shape.Rect(n, n)

#guard square.check shapes []

-- `EIndNew` evaluates one expression per thing the constructor carries and keeps the values in that
-- order, under the two names it was given.
example : FuncDecl.Apply square shapes [] [.int 2] (.ind "Shape" "Rect" [.int 2, .int 2]) :=
  .EApply _ (.cons "n" (.int 2) .nil)
    (.EIndNew (vs := [.int 2, .int 2]) _ _ _ rfl (by
      rintro p hp
      simp at hp
      rcases hp with rfl | rfl <;> exact .EVarRef "n" rfl))

example (v : Value) (h : FuncDecl.Apply square shapes [] [.int 2] v) :
    v.HasType shapes (.ind "Shape") :=
  h.hasType Globals.wellTyped_nil (by simp [square, Color, Shape, shapes, List.lookup])

/-! ### Recursion

A constructor may carry the very type it belongs to, and a global may call itself, so a recursive
function over a recursive type needs nothing this language does not already have. -/

/-- A binary tree with an `int` at each branch. -/
lgtm private inductive Tree { Leaf, Node(inductive Tree, int, inductive Tree) }

private def trees : TypeDecls := { is := Inductives.ofDecls [Tree] }

/-- The sum of `t`'s labels. -/
lgtm private def total (t : inductive Tree) : int :=
  match t with | Leaf => 0 | Node(l, n, r) => total(l) + n + total(r)

private def forest : Globals := Globals.ofDecls [total]

-- The declaration checks against a context holding itself, exactly as `countdown` does: it is the
-- table that makes the recursive call resolve, and the recursive *type* needs nothing at all, since
-- `Tree` is resolved where it is mentioned rather than where it was declared.
#guard Globals.check trees forest
#guard !total.check trees []

/-- `Leaf` carries nothing, so the empty alternative runs and the recursion stops. -/
private theorem hasType_leaf : Value.HasType trees (.ind "Tree" "Leaf" []) (.ind "Tree") :=
  .ind rfl rfl rfl (by simp)

example : FuncDecl.Apply total trees forest [.ind "Tree" "Leaf" []] (.int 0) :=
  .EApply _ (.cons "t" hasType_leaf .nil) (.EIndMatch _ _ (.EVarRef "t" rfl) rfl (.EIntLit 0))

/-! ### A program with inductive types

The same declarations again, read as a source file: a `Program` carries its inductive types beside
its structure types and its declarations, and `Program.typeDecls` is the bundle its bodies are
checked and run against. -/

private def shapeProgram : Program where
  funcDecls := [area, square]
  inductiveDecls := [Color, Shape]

example : shapeProgram.typeDecls = shapes := rfl

#guard shapeProgram.check

-- The type declarations are what make it check: without them both bodies mention a type that names
-- nothing.
#guard !({ shapeProgram with inductiveDecls := [] } : Program).check

-- A program resolves the inductive names it declares, and no two of them share a name — the
-- counterpart of `StructNamesUnique` for the other kind of type.
example : shapeProgram.lookupInductive "Shape" = some Shape := rfl
example : shapeProgram.lookupInductive "Hue" = none := rfl
example : shapeProgram.InductiveNamesUnique := by decide
example : ¬ ({ shapeProgram with inductiveDecls := [Color, Color] }
    : Program).InductiveNamesUnique := by decide
example : shapeProgram.lookupInductive Shape.name = some Shape :=
  shapeProgram.lookupInductive_self (by decide) (by simp [shapeProgram])

-- And no declaration of the program names a constructor twice, which is the condition inside a
-- declaration rather than across them: it is what makes `Shape`'s every constructor reachable, and
-- what keeps a match on it from having to write an alternative that can never run.
example : shapeProgram.CtorNamesUnique := by decide
example : ¬ ({ shapeProgram with
    inductiveDecls := [{ name := "Shape", constructors := [("Circle", [.int]), ("Circle", [])] }] }
    : Program).CtorNamesUnique := by decide

-- `check` is where that is enforced, as it is for a repeated field: the extra type below is one no
-- body mentions, so what turns the program down is the repeated constructor and nothing else.
#guard !({ shapeProgram with inductiveDecls := [Color, Shape,
  { name := "Dup", constructors := [("Red", []), ("Red", [.int])] }] } : Program).check
#guard ({ shapeProgram with inductiveDecls := [Color, Shape,
  { name := "Dup", constructors := [("Red", []), ("Crimson", [.int])] }] } : Program).check

/-- `shapeProgram` checks, which is a property of the program alone. -/
private theorem shapeProgram.wellTyped : shapeProgram.WellTyped := by
  refine Globals.wellTyped_of_forall fun p hp => ?_
  simp only [Program.globals, shapeProgram, Globals.ofDecls, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;>
    simp [area, square, Color, Shape, Program.globals, Program.typeDecls, Program.structs,
      Program.inductives, shapeProgram, Globals.ofDecls, Structs.ofDecls, Inductives.ofDecls,
      FuncDecl.ty, List.lookup, Expression.altsExhaustive, List.isPerm]

-- Running it is calling one of its names, and soundness at the top covers an inductive result type
-- like any other.
example : shapeProgram.Apply "area" [.ind "Shape" "Rect" [.int 3, .int 4]] (.int 7) :=
  .call _ rfl eval_area

example (v : Value) (args : List Value) (h : shapeProgram.Apply "square" args v) :
    v.HasType shapeProgram.typeDecls (.ind "Shape") :=
  h.hasType shapeProgram.wellTyped rfl

end Tests
