module

import LgtmDeepLean.Lang.Eval
import LgtmDeepLean.Lang.Syntax
meta import LgtmDeepLean.Lang.Eval
meta import LgtmDeepLean.Lang.Syntax

/-! # Tests for the relational semantics

Worked examples of `Eval`, `FuncDecl.Apply`, and `Program.Apply`: what each syntactic form
evaluates to, what it gets stuck on, and how a proof about a declaration is carried out through the
relation rather than about the `Expression` itself. -/

/-- Add `x` to one less than `y`. -/
@[lgtm] private def addPred as"add-pred"(x : int)(y : int) : int := x + (y - 1)

-- This is a simple proof demonstrating how proofs work through the
-- relational evaluator
private theorem addPred.trivial_positive (x y res : Value) (hXPos : ∀ xv, .int xv = x → xv >= 1)
    (hYPos : ∀ yv, .int yv = y → yv >= 1) (hRes : FuncDecl.Apply addPred {} [] [x, y] res) :
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
          | EIntLit
            _ =>
            simp [addPred, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
              List.lookup] at hlx hly
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
example (v : Value) : ¬FuncDecl.Apply addPred {} [] [.int 2] v := by
  rintro ⟨-, hargs, -⟩
  cases hargs with
  | cons _ _ hrest => cases hrest

example (v : Value) : ¬FuncDecl.Apply addPred {} [] [.int 2, .int 5, .int 8] v := by
  rintro ⟨-, hargs, -⟩
  cases hargs with
  | cons _ _ hrest =>
    cases hrest with
    | cons _ _ hrest => cases hrest

/-- Put `x` on the front of `xs`. -/
@[lgtm] private def cons(x : int)(xs : list int) : list int := x :: xs

/-- A one-element list is homogeneous for the reason its only element is. -/
private theorem hasType_singleton {v : Value} {t : Ty} (h : v.HasType td t) :
    Value.HasType td (.list [v]) (.list t) :=
  .list (by simpa using h)

example : FuncDecl.Apply cons {} [] [.int 1, .list [.int 2]] (.list [.int 1, .int 2]) :=
  .EApply _ (.cons "x" (.int 1) (.cons "xs" (hasType_singleton (.int 2)) .nil))
    (.ECons _ _ (.EVarRef "x" rfl) (.EVarRef "xs" rfl))

-- An argument of the wrong type is now rejected at the call itself, rather than getting the body
-- stuck once it is looked up.
example (v : Value) : ¬FuncDecl.Apply cons {} [] [.int 1, .int 2] v := by
  rintro ⟨-, hargs, -⟩
  cases hargs with
  | cons _ _ hrest =>
    cases hrest with
    | cons _ hv _ => cases hv

/-- Reverse `xs` with `x` on the front. -/
@[lgtm] private def revCons as"rev-cons"(x : int)(xs : list int) : list int := reverse(x :: xs)

/-- A list of `int`s is homogeneous at `.list .int`, whatever its length. -/
private theorem hasType_intList {is : List Int} :
    Value.HasType td (.list (is.map .int)) (.list .int) :=
  .list (by simp)

-- `EListReverse` runs on the list `ECons` has just built, so the element pushed on the front comes
-- back last.
example :
    FuncDecl.Apply revCons {} [] [.int 1, .list [.int 2, .int 3]]
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
example : ¬({ revCons with body := [lgtm| reverse x] } : FuncDecl).WellTyped {} [] := by
  simp [revCons, List.lookup]

/-- Reverse `xs` twice, which gives `xs` back. -/
@[lgtm] private def reverseTwice as"reverse-twice"(xs : list int) : list int := reverse(reverse xs)

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
      | EVarRef _
        hlx =>
        simp [reverseTwice, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup] at hlx
        grind

/-- The length of `xs` with `x` on the front. -/
@[lgtm] private def lengthCons as"length-cons"(x : int)(xs : list int) : int := length(x :: xs)

-- `EListLength` counts the list `ECons` has just built, so the element pushed on the front is
-- counted along with the ones that were already there.
example : FuncDecl.Apply lengthCons {} [] [.int 1, .list [.int 2, .int 3]] (.int 3) :=
  .EApply _ (.cons "x" (.int 1) (.cons "xs" (hasType_intList (is := [2, 3])) .nil))
    (.EListLength (vs := [.int 1, .int 2, .int 3]) _
      (.ECons _ _ (.EVarRef "x" rfl) (.EVarRef "xs" rfl)))

-- A length is an `int` whatever the list held, so soundness gives the declared result type back
-- without any reasoning about the elements.
example (v : Value) (h : FuncDecl.Apply lengthCons {} [] [.int 1, .list [.int 2, .int 3]] v) :
    v.HasType {} .int :=
  h.hasType Globals.wellTyped_nil (by simp [lengthCons, List.lookup])

-- Only a list has a length, so a body taking the length of one of the `int` parameters does not
-- check — and neither does one whose result is declared to be the list it counted.
example : ¬({ lengthCons with body := [lgtm| length x] } : FuncDecl).WellTyped {} [] := by
  simp [lengthCons, List.lookup]

example : ¬({ lengthCons with resultType := [lgtm_ty| list int] } : FuncDecl).WellTyped {} [] := by
  simp [lengthCons, List.lookup]

/-- The length of `xs` reversed. -/
@[lgtm] private def lengthOfReverse as"length-of-reverse"(xs : list int) : int := length(reverse xs)

/-- Reversing a list does not change its length.

Inverting the `EListLength` step and the `EListReverse` under it down to the `EVarRef` that read
`xs` leaves exactly `List.length_reverse`, so this is a property of the program proved from the
evaluator rather than from any one input — the same shape as `reverseTwice.eq_self`, over the two
list forms composed instead of one twice. -/
private theorem lengthOfReverse.eq_length {vs : List Value} {res : Value}
    (h : FuncDecl.Apply lengthOfReverse {} [] [.list vs] res) : res = .int vs.length := by
  obtain ⟨-, -, hbody⟩ := h
  cases hbody with
  | EListLength _ h₁ =>
    cases h₁ with
    | EListReverse _ h₂ =>
      cases h₂ with
      | EVarRef _
        hlx =>
        simp [lengthOfReverse, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup] at hlx
        grind

/-! A mapping over a list is a call per element: the element is the one argument, `ArgsHaveType` is
what holds it to the closure's parameter, and the body is evaluated in the environment the closure
captured rather than in the one the mapping was written in.

`EHashmapMap` with the key taken away — one argument where that has two, and the lengths agreeing
where that has the keys agreeing.  What can go wrong is what a call can: a second operand that is not
a function at all, and a function the element does not fit. -/

-- An empty list maps to an empty list: there is no element for the function to be applied to, so
-- both premises over the elements are vacuous and the function is never entered.
example : Eval {} ∅ [lgtm| map [: int] (fun (x : int) => x + 1)] (.list []) :=
  .EListMap (vs' := []) _ _ (.ENil _) (.ELam _ _) rfl (by simp) (by simp)

-- One element is one call, and what it produced takes that element's place: the result is as long as
-- the list it came from, which is the whole of what a mapping says about the shape of either.
example : Eval {} ∅ [lgtm| map [1 : int] (fun (x : int) => x + 1)] (.list [.int 2]) :=
  .EListMap (vs' := [.int 2]) _ _ (.ECons _ _ (.EIntLit 1) (.ENil _)) (.ELam _ _) rfl
    (by rintro p hp
        simp at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact .cons "x" (.int 1) .nil)
    (by rintro p hp
        simp at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact .EPlus (n₁ := 1) (n₂ := 1) _ _ (.EVarRef "x" rfl) (.EIntLit 1))

-- The function's result is what the elements become, so a mapping can produce a list of a type
-- nothing in the list it was given had — which is the one thing a list's mapping does that a
-- hashmap's cannot do to its keys.
example : Eval {} ∅ [lgtm| map [1 : int] (fun (x : int) => "a")] (.list [.string "a"]) :=
  .EListMap (vs' := [.string "a"]) _ _ (.ECons _ _ (.EIntLit 1) (.ENil _)) (.ELam _ _) rfl
    (by rintro p hp
        simp at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact .cons "x" (.int 1) .nil)
    (by rintro p hp
        simp at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact .EStringLit "a")

-- A second operand that is not a function leaves this stuck, which is one of the two things that
-- can go wrong here and is exactly what typing rules out.
example (v : Value) : ¬Eval {} ∅ [lgtm| map[ : int]1] v := by
  intro h
  cases h with
  | EListMap _ _ _ hf _ _ _ => cases hf

/-- Every element of `xs` with one added to it: the shortest declaration the form is in, and the one
place a list is read element by element rather than whole. -/
@[lgtm] private def bumpAll as "bump-all" (xs : list int) : list int :=
  map xs (fun (x : int) => x + 1)

#guard (bumpAll.check {} []).isOk

-- The closure the function evaluates to captures the call's environment, so the body runs over the
-- parameter of the `fun` in front of `xs` — the same way a call into a closure runs it.
example : FuncDecl.Apply bumpAll {} [] [.list [.int 1, .int 2]] (.list [.int 2, .int 3]) :=
  .EApply _ (.cons "xs" (hasType_intList (is := [1, 2])) .nil)
    (.EListMap (vs' := [.int 2, .int 3]) _ _ (.EVarRef "xs" rfl) (.ELam _ _) rfl
      (by
        rintro p hp
        simp at hp
        rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact .cons "x" (by constructor) .nil)
      (by
        rintro p hp
        simp at hp
        rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact .EPlus (n₁ := 1) (n₂ := 1) _ _ (.EVarRef "x" rfl) (.EIntLit 1)
        · exact .EPlus (n₁ := 2) (n₂ := 1) _ _ (.EVarRef "x" rfl) (.EIntLit 1)))

-- An empty list is the one argument that needs neither premise, since there is no element to apply
-- the function to.
example : FuncDecl.Apply bumpAll {} [] [.list []] (.list []) :=
  .EApply _ (.cons "xs" (hasType_intList (is := [])) .nil)
    (.EListMap (vs' := []) _ _ (.EVarRef "xs" rfl) (.ELam _ _) rfl (by simp) (by simp))

-- Soundness covers the form: the declared list type comes back whatever the list held, with the
-- element type read off the function's body rather than carried through from the argument.
example (vs : List Value) (v : Value) (h : FuncDecl.Apply bumpAll {} [] [.list vs] v) :
    v.HasType {} (.list .int) :=
  h.hasType Globals.wellTyped_nil (by simp [bumpAll])

-- A function the element does not fit is the other thing that can go wrong: the element is the one
-- argument, so `ArgsHaveType` turns down a function expecting a `string` exactly as a call with the
-- wrong argument type is turned down.
example (v : Value) :
    ¬ Eval {} ⟨[("xs", .list [.int 1])], []⟩ [lgtm| map xs (fun (x : string) => x)] v := by
  intro h
  cases h with
  | @EListMap _ _ _ _ _ _ vs' _ _ hl hf hlen hat _ =>
      cases hl with
      | EVarRef _ hlx =>
          cases hf with
          | ELam _ _ =>
              simp [Env.lookup, List.lookup] at hlx
              subst hlx
              -- The result is as long as the list it was given, so it has one element, and the
              -- argument that element is passed as is an `int` the function has no parameter for.
              obtain ⟨w, rfl⟩ : ∃ w, vs' = [w] := by
                cases vs' with
                | nil => simp at hlen
                | cons w rest =>
                    cases rest with
                    | nil => exact ⟨w, rfl⟩
                    | cons _ _ => simp at hlen
              cases hat (.int 1, w) (by simp) with
              | cons _ hv _ => cases hv

/-- What a mapping over a list means, for every list rather than for one: the list it produces is as
long as the list it was given.

This is the fact a proof about a mapped list carries on with, the way `bump.keys_of_eval` is for a
mapped map — and it is the counterpart of that one, since a length is what a list has in place of a
set of keys.  Inverting the rule leaves exactly that equality: the elements are what the calls
produced, and the length is what no call was made about. -/
private theorem bumpAll.length_of_eval {vs vs' : List Value}
    (h : Eval {} ⟨[("xs", .list vs)], []⟩
      [lgtm| map xs (fun (x : int) => x + 1)] (.list vs')) :
    vs.length = vs'.length := by
  cases h with
  | EListMap _ _ hl _ hlen _ _ =>
      cases hl with
      | EVarRef _ hlx =>
          simp [Env.lookup, List.lookup] at hlx
          subst hlx
          exact hlen

/-! A flat mapping over a list is the same call again, and the results run together: each call
produces a list, and `List.flatten` puts those lists one after another in the order the elements were
in.

`EListMap` with a `List (List Value)` where that has a `List Value`, which is the whole of the
difference.  The lengths that agree are still the operand's and the calls' — one list produced per
element — so what the form does *not* guarantee is how long its result is, and that is what these
examples are for.  What can go wrong is what a mapping's calls can: a second operand that is not a
function, and a function the element does not fit. -/

-- An empty list flat maps to an empty list: there is no element for the function to be applied to,
-- so both premises over the elements are vacuous and the function is never entered.
example : Eval {} ∅ [lgtm| flatMap [: int] (fun (x : int) => [x, x : int])] (.list []) :=
  .EListFlatMap (vss := []) _ _ (.ENil _) (.ELam _ _) rfl (by simp) (by simp)

-- One element is one call, and the list that call produced takes that element's place: two elements
-- out of one is the thing no mapping can do, since a mapping's result is as long as its operand.
example :
    Eval {} ∅ [lgtm| flatMap [1 : int] (fun (x : int) => [x, x : int])]
      (.list [.int 1, .int 1]) :=
  .EListFlatMap (vss := [[.int 1, .int 1]]) _ _ (.ECons _ _ (.EIntLit 1) (.ENil _)) (.ELam _ _) rfl
    (by rintro p hp
        simp at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact .cons "x" (.int 1) .nil)
    (by rintro p hp
        simp at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact .ECons _ _ (.EVarRef "x" rfl) (.ECons _ _ (.EVarRef "x" rfl) (.ENil _)))

-- And the other direction: a call returning the empty list drops the element it was given, so a
-- non-empty list flat maps to an empty one.
example : Eval {} ∅ [lgtm| flatMap [1 : int] (fun (x : int) => [: int])] (.list []) :=
  .EListFlatMap (vss := [[]]) _ _ (.ECons _ _ (.EIntLit 1) (.ENil _)) (.ELam _ _) rfl
    (by rintro p hp
        simp at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact .cons "x" (.int 1) .nil)
    (by rintro p hp
        simp at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact .ENil _)

-- A second operand that is not a function leaves this stuck, exactly as it leaves a mapping stuck.
example (v : Value) : ¬Eval {} ∅ [lgtm| flatMap[ : int]1] v := by
  intro h
  cases h with
  | EListFlatMap _ _ _ hf _ _ _ => cases hf

/-- Every element of `xs` twice over: the shortest declaration the form is in, and the one place a
list comes back longer than it went in. -/
@[lgtm] private def dupAll as "dup-all" (xs : list int) : list int :=
  flatMap xs (fun (x : int) => [x, x : int])

#guard (dupAll.check {} []).isOk

-- The closure the function evaluates to captures the call's environment, the same way a mapping's
-- does, and the lists its calls produced come back in the order the elements were in.
example :
    FuncDecl.Apply dupAll {} [] [.list [.int 1, .int 2]]
      (.list [.int 1, .int 1, .int 2, .int 2]) :=
  .EApply _ (.cons "xs" (hasType_intList (is := [1, 2])) .nil)
    (.EListFlatMap (vss := [[.int 1, .int 1], [.int 2, .int 2]]) _ _ (.EVarRef "xs" rfl)
      (.ELam _ _) rfl
      (by
        rintro p hp
        simp at hp
        rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact .cons "x" (by constructor) .nil)
      (by
        rintro p hp
        simp at hp
        rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          exact .ECons _ _ (.EVarRef "x" rfl) (.ECons _ _ (.EVarRef "x" rfl) (.ENil _))))

-- Soundness covers the form: the declared list type comes back whatever the list held, with the
-- element type read out of what the function returns rather than off the function's result whole.
example (vs : List Value) (v : Value) (h : FuncDecl.Apply dupAll {} [] [.list vs] v) :
    v.HasType {} (.list .int) :=
  h.hasType Globals.wellTyped_nil (by simp [dupAll])

/-- What a flat mapping means, for every list rather than for one: this one doubles, so the list it
produces is twice as long as the list it was given.

`bumpAll.length_of_eval`'s counterpart, and the reason the two forms are not one: a mapping's
length equality is a premise of the rule and holds whatever the function is, where this is a fact
about *this* function and comes out of what its calls produced.  Inverting the rule leaves the
lengths of the calls' lists to be added up, which is what `List.length_flatten` does. -/
private theorem dupAll.length_of_eval {vs vs' : List Value}
    (h : Eval {} ⟨[("xs", .list vs)], []⟩
      [lgtm| flatMap xs (fun (x : int) => [x, x : int])] (.list vs')) :
    vs'.length = 2 * vs.length := by
  cases h with
  | @EListFlatMap _ _ _ _ _ _ vss _ _ hl hf hlen _ hev =>
      cases hl with
      | EVarRef _ hlx =>
          cases hf with
          | ELam _ _ =>
              simp [Env.lookup, List.lookup] at hlx
              subst hlx
              -- Every call produced a two-element list, which is what the body being a two-element
              -- literal is read off: inverting its evaluation is what pins the length down, and it
              -- needs the closure's body in hand rather than the opaque one the rule mentions.
              have hws : ∀ p ∈ vs.zip vss, p.2.length = 2 := by
                rintro ⟨w, ws⟩ hp
                cases hev (w, ws) hp with
                | ECons _ _ _ htl =>
                    cases htl with
                    | ECons _ _ _ htl' =>
                        cases htl' with
                        | ENil _ => rfl
              -- The lengths are two apiece over as many calls as there were elements, so the sum
              -- the flattening's length comes to is what the list's own length doubles to.
              rw [List.length_flatten, ← List.map_snd_zip (Nat.le_of_eq hlen.symm), List.map_map]
              simp only [Function.comp_def]
              rw [List.map_congr_left hws]
              simp [List.map_const', List.sum_replicate_nat, List.length_zip, hlen, Nat.mul_comm]

/-! A sort is a call per element too, and the same call a mapping makes: the element is the one
argument, `ArgsHaveType` holds it to the closure's parameter, and the body runs in the environment
the closure captured.  What the calls produce is the difference — a key apiece rather than an
element — so the list that comes back holds the values that went in, in the order their keys put
them in.

`Value.sortByKey` is what puts them there, and it is a function rather than a premise saying the
result is sorted: a key several elements share would leave such a premise with several results and
`Eval` with none.  It is also why the examples below convert: the rule hands back
`Value.sortByKey` applied to the pairs, and what that comes to is a `simp` away rather than
something the elaborator sees.

What can go wrong is what a mapping's two operands can, plus one thing of its own: a key the
ordering has no answer about. -/

-- An empty list sorts to an empty list: there is no element for the projection to be applied to, so
-- every premise over the elements is vacuous and the function is never entered.
example : Eval {} ∅ [lgtm| sortOn [ : int] (fun (x : int) => x)] (.list []) := by
  have h : Eval {} ∅ [lgtm| sortOn [ : int] (fun (x : int) => x)]
      (.list ((Value.sortByKey (([] : List Value).zip [])).map Prod.fst)) :=
    .EListSortOn (ks := []) _ _ (.ENil _) (.ELam _ _) rfl (by simp) (by simp) (by simp)
  simpa [Value.sortByKey] using h

-- Projecting an element onto itself orders the list by its own elements, so one already in order
-- comes back as it was.
example : Eval {} ∅ [lgtm| sortOn [1, 2 : int] (fun (x : int) => x)] (.list [.int 1, .int 2]) := by
  have h : Eval {} ∅ [lgtm| sortOn [1, 2 : int] (fun (x : int) => x)]
      (.list ((Value.sortByKey ([Value.int 1, .int 2].zip [Value.int 1, .int 2])).map Prod.fst)) := by
    refine .EListSortOn (ks := [.int 1, .int 2]) _ _
      (.ECons _ _ (.EIntLit 1) (.ECons _ _ (.EIntLit 2) (.ENil _))) (.ELam _ _) rfl ?_ ?_ ?_
    · rintro p hp
      simp at hp
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact .cons "x" (by constructor) .nil
    · rintro p hp
      simp at hp
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact .EVarRef "x" rfl
    · rintro k hk k' hk'
      simp at hk hk'
      rcases hk with rfl | rfl <;> rcases hk' with rfl | rfl <;> simp [Value.cmp?]
  simpa [Value.sortByKey] using h

-- A key that runs the other way puts the list the other way round, and the elements come back whole:
-- it is the keys that were compared, and they are dropped once the order is settled.
example : Eval {} ∅ [lgtm| sortOn [1, 2 : int] (fun (x : int) => 0 - x)] (.list [.int 2, .int 1]) := by
  have h : Eval {} ∅ [lgtm| sortOn [1, 2 : int] (fun (x : int) => 0 - x)]
      (.list
        ((Value.sortByKey ([Value.int 1, .int 2].zip [Value.int (0 - 1), .int (0 - 2)])).map
          Prod.fst)) := by
    refine .EListSortOn (ks := [.int (0 - 1), .int (0 - 2)]) _ _
      (.ECons _ _ (.EIntLit 1) (.ECons _ _ (.EIntLit 2) (.ENil _))) (.ELam _ _) rfl ?_ ?_ ?_
    · rintro p hp
      simp at hp
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact .cons "x" (by constructor) .nil
    · rintro p hp
      simp at hp
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .EMinus (n₁ := 0) (n₂ := 1) _ _ (.EIntLit 0) (.EVarRef "x" rfl)
      · exact .EMinus (n₁ := 0) (n₂ := 2) _ _ (.EIntLit 0) (.EVarRef "x" rfl)
    · rintro k hk k' hk'
      simp at hk hk'
      rcases hk with rfl | rfl <;> rcases hk' with rfl | rfl <;> simp [Value.cmp?]
  simpa [Value.sortByKey] using h

-- A projection that answers the same key for every element leaves the list alone, which is what
-- being stable comes to: equal keys decide nothing, so the order they came in is the order they
-- come back in.
example : Eval {} ∅ [lgtm| sortOn [2, 1 : int] (fun (x : int) => 0)] (.list [.int 2, .int 1]) := by
  have h : Eval {} ∅ [lgtm| sortOn [2, 1 : int] (fun (x : int) => 0)]
      (.list ((Value.sortByKey ([Value.int 2, .int 1].zip [Value.int 0, .int 0])).map Prod.fst)) := by
    refine .EListSortOn (ks := [.int 0, .int 0]) _ _
      (.ECons _ _ (.EIntLit 2) (.ECons _ _ (.EIntLit 1) (.ENil _))) (.ELam _ _) rfl ?_ ?_ ?_
    · rintro p hp
      simp at hp
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact .cons "x" (by constructor) .nil
    · rintro p hp
      simp at hp
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact .EIntLit 0
    · rintro k hk k' hk'
      simp at hk hk'
      subst hk
      subst hk'
      simp [Value.cmp?]
  simpa [Value.sortByKey] using h

-- A second operand that is not a function leaves this stuck, exactly as it leaves a mapping stuck.
example (v : Value) : ¬Eval {} ∅ [lgtm| sortOn[ : int]1] v := by
  intro h
  cases h with
  | EListSortOn _ _ _ hf _ _ _ _ => cases hf

-- A key the ordering has no answer about is the thing that can go wrong here and nowhere else: a
-- `bool` is a value `Value.beq?` answers for and `Value.cmp?` does not, so a projection returning
-- one leaves the sort stuck — which is exactly what `Ty.orderable` on the projection's result type
-- rules out.
example (v : Value) : ¬Eval {} ∅ [lgtm| sortOn [1 : int] (fun (x : int) => true)] v := by
  intro h
  cases h with
  | @EListSortOn _ _ _ _ _ _ ks _ _ hl hf hlen _ hev hcmp =>
      cases hl with
      | ECons _ _ h₁ h₂ =>
          cases h₁ with
          | EIntLit _ =>
          cases h₂ with
          | ENil _ =>
              cases hf with
              | ELam _ _ =>
                  obtain ⟨k, rfl⟩ : ∃ k, ks = [k] := by
                    cases ks with
                    | nil => simp at hlen
                    | cons k rest =>
                        cases rest with
                        | nil => exact ⟨k, rfl⟩
                        | cons _ _ => simp at hlen
                  cases hev (.int 1, k) (by simp) with
                  | EBoolLit _ =>
                    simpa [Value.cmp?] using
                      hcmp (.bool true) (by simp) (.bool true) (by simp)

/-- `xs` largest first: the shortest declaration the form is in, and the one place a list is
reordered by something read off its elements rather than by where they were. -/
@[lgtm] private def sortDesc as "sort-desc" (xs : list int) : list int :=
  sortOn xs (fun (x : int) => 0 - x)

#guard (sortDesc.check {} []).isOk

-- The closure the projection evaluates to captures the call's environment, the way a mapping's
-- does, so the keys are computed over the parameter of the `fun` rather than over `xs`.
example : FuncDecl.Apply sortDesc {} [] [.list [.int 1, .int 2]] (.list [.int 2, .int 1]) := by
  have h :
    FuncDecl.Apply sortDesc {} [] [.list [.int 1, .int 2]]
      (.list
        ((Value.sortByKey ([Value.int 1, .int 2].zip [Value.int (0 - 1), .int (0 - 2)])).map
          Prod.fst)) := by
    refine .EApply _ (.cons "xs" (hasType_intList (is := [1, 2])) .nil) ?_
    refine
      .EListSortOn (ks := [.int (0 - 1), .int (0 - 2)]) _ _ (.EVarRef "xs" rfl) (.ELam _ _) rfl ?_
        ?_ ?_
    · rintro p hp
      simp at hp
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact .cons "x" (by constructor) .nil
    · rintro p hp
      simp at hp
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .EMinus (n₁ := 0) (n₂ := 1) _ _ (.EIntLit 0) (.EVarRef "x" rfl)
      · exact .EMinus (n₁ := 0) (n₂ := 2) _ _ (.EIntLit 0) (.EVarRef "x" rfl)
    · rintro k hk k' hk'
      simp at hk hk'
      rcases hk with rfl | rfl <;> rcases hk' with rfl | rfl <;> simp [Value.cmp?]
  simpa [Value.sortByKey] using h

-- Soundness covers the form, and it is the element type that comes back rather than the key's: the
-- projection returns an `int` here too, so the declaration below is where the two part company.
example (vs : List Value) (v : Value) (h : FuncDecl.Apply sortDesc {} [] [.list vs] v) :
    v.HasType {} (.list .int) :=
  h.hasType Globals.wellTyped_nil (by simp [sortDesc])

/-- `sortDesc` with a `string` key, which is where a sort's two types part company: the key is what
the order was decided by, and the elements come back at the type they went in at. -/
private def sortByLabel : FuncDecl :=
  { sortDesc with body := [lgtm| sortOn xs (fun (x : int) => "a")] }

#guard (sortByLabel.check {} []).isOk

-- So declaring the key's type as the result type does not check, where the same body under
-- `map` would need exactly that.
#guard !(({ sortByLabel with resultType := [lgtm_ty| list string] } : FuncDecl).check {} []).isOk

-- Only a list can be sorted, and only by a key with an ordering: a body sorting by a `bool` is
-- turned down where the same body under `map` would be accepted.
example : ¬({ sortDesc with body := [lgtm| sortOn n f] } : FuncDecl).WellTyped {} [] := by
  simp [sortDesc, List.lookup]

example :
    ¬({ sortDesc with body := [lgtm| sortOn xs (fun (x : int) => true)] } : FuncDecl).WellTyped {}
        [] := by
  simp [sortDesc, List.lookup]

/-- What a sort means, for every list rather than for one: the list it produces is as long as the
list it was given.

The counterpart of `bumpAll.length_of_eval`, and for the same reason — a length is what a list has
in place of a set of keys — except that here it is not a premise of the rule: the result is the
pairs sorted, and `Value.length_sortByKey` is what says a sort rearranges them and nothing else. -/
private theorem sortDesc.length_of_eval {vs vs' : List Value}
    (h : Eval {} ⟨[("xs", .list vs)], []⟩ [lgtm| sortOn xs (fun (x : int) => 0 - x)] (.list vs')) :
    vs.length = vs'.length := by
  cases h with
  | @EListSortOn _ _ _ _ _ _ ks _ _ hl _ hlen _ _ _ =>
      cases hl with
      | EVarRef _ hlx =>
          simp [Env.lookup, List.lookup] at hlx
          subst hlx
          simp [hlen]

/-! A sort by a comparison is a call per *pair* of elements, which is the one thing no other rule
does: a projection is handed one element and a comparison two.  What the calls produce is the answer
itself rather than a key, so there is no premise over them — a `bool` is a `bool` — and the list that
comes back holds the values that went in, in the order those answers put them.

`Value.sortWith` needs a `Value → Value → Bool` and a DSL function is not one, so the rule asks for
a Lean function and holds it to the DSL one at every pair of elements.  That is what the examples
below supply as `cmp`, and `leValues` is what it comes to wherever the comparison written out is the
DSL's own `<=`.

What can go wrong is what a mapping's two operands can, plus one thing of its own: a comparison that
answers with something other than a `bool` is one no `cmp` agrees with, so there is no such function
to be had and the sort has no value — which is `sortOn`'s incomparable key in the place the two forms
differ. -/

/-- `x <= y` as a function on values: what a DSL comparison written `a <= b` answers, read as the
`Bool` `Value.sortWith` takes.

The same comparison `Value.sortByKey` is defined over, which is no accident: `sortBy` with this is
`sortOn` by the elements themselves, and the point of the form is the comparisons that are *not*
this one. -/
private def leValues (x y : Value) : Bool :=
  Value.le? x y == some true

-- An empty list sorts to an empty list: there is no pair for the comparison to be asked about, so
-- both premises over the elements are vacuous and the function is never entered.
example : Eval {} ∅ [lgtm| sortBy [ : int] (fun (a : int) (b : int) => a <= b)] (.list []) := by
  have h : Eval {} ∅ [lgtm| sortBy [ : int] (fun (a : int) (b : int) => a <= b)]
      (.list (Value.sortWith leValues [])) :=
    .EListSortBy (cmp := leValues) _ _ (.ENil _) (.ELam _ _) (by simp) (by simp)
  simpa [Value.sortWith] using h

-- A comparison that is the elements' own ordering puts them in it, so a list out of order comes back
-- in order.
example : Eval {} ∅ [lgtm| sortBy [2, 1 : int] (fun (a : int) (b : int) => a <= b)]
    (.list [.int 1, .int 2]) := by
  have h : Eval {} ∅ [lgtm| sortBy [2, 1 : int] (fun (a : int) (b : int) => a <= b)]
      (.list (Value.sortWith leValues [.int 2, .int 1])) := by
    refine .EListSortBy (cmp := leValues) _ _
      (.ECons _ _ (.EIntLit 2) (.ECons _ _ (.EIntLit 1) (.ENil _))) (.ELam _ _) ?_ ?_
    · rintro a ha b hb
      simp at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        exact .cons "a" (by constructor) (.cons "b" (by constructor) .nil)
    · rintro a ha b hb
      simp at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        exact .ELe _ _ (.EVarRef "a" rfl) (.EVarRef "b" rfl) (by simp [leValues])
  simpa [Value.sortWith, leValues] using h

-- A comparison read the other way round puts the list the other way round, and it is the comparison
-- that was turned around rather than a key: the two operands are the pair it was asked about.
example : Eval {} ∅ [lgtm| sortBy [1, 2 : int] (fun (a : int) (b : int) => b <= a)]
    (.list [.int 2, .int 1]) := by
  have h : Eval {} ∅ [lgtm| sortBy [1, 2 : int] (fun (a : int) (b : int) => b <= a)]
      (.list (Value.sortWith (fun x y => leValues y x) [.int 1, .int 2])) := by
    refine .EListSortBy (cmp := fun x y => leValues y x) _ _
      (.ECons _ _ (.EIntLit 1) (.ECons _ _ (.EIntLit 2) (.ENil _))) (.ELam _ _) ?_ ?_
    · rintro a ha b hb
      simp at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        exact .cons "a" (by constructor) (.cons "b" (by constructor) .nil)
    · rintro a ha b hb
      simp at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        exact .ELe _ _ (.EVarRef "b" rfl) (.EVarRef "a" rfl) (by simp [leValues])
  simpa [Value.sortWith, leValues] using h

-- A comparison that answers the same for every pair leaves the list alone, which is what being
-- stable comes to: a pair it does not separate keeps the order it came in.
example : Eval {} ∅ [lgtm| sortBy [2, 1 : int] (fun (a : int) (b : int) => true)]
    (.list [.int 2, .int 1]) := by
  have h : Eval {} ∅ [lgtm| sortBy [2, 1 : int] (fun (a : int) (b : int) => true)]
      (.list (Value.sortWith (fun _ _ => true) [.int 2, .int 1])) := by
    refine .EListSortBy (cmp := fun _ _ => true) _ _
      (.ECons _ _ (.EIntLit 2) (.ECons _ _ (.EIntLit 1) (.ENil _))) (.ELam _ _) ?_ ?_
    · rintro a ha b hb
      simp at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        exact .cons "a" (by constructor) (.cons "b" (by constructor) .nil)
    · rintro a ha b hb
      simp at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> exact .EBoolLit true
  simpa [Value.sortWith] using h

-- A second operand that is not a function leaves this stuck, exactly as it leaves a mapping and the
-- other sort stuck.
example (v : Value) : ¬Eval {} ∅ [lgtm| sortBy[ : int]1] v := by
  intro h
  cases h with
  | EListSortBy _ _ _ hf _ _ => cases hf

-- A comparison that does not answer with a `bool` is the thing that can go wrong here and nowhere
-- else: `cmp` is a `Bool`-valued function, so there is none that agrees with a body evaluating to an
-- `int`, and the sort has no value at all — which is exactly what the comparison's result type being
-- held to `bool` rules out.
example (v : Value) : ¬Eval {} ∅ [lgtm| sortBy [1 : int] (fun (a : int) (b : int) => 0)] v := by
  intro h
  cases h with
  | EListSortBy _ _ hl hf _ hev =>
      cases hl with
      | ECons _ _ h₁ h₂ =>
          cases h₁ with
          | EIntLit _ =>
          cases h₂ with
          | ENil _ =>
              cases hf with
              | ELam _ _ => cases hev (.int 1) (by simp) (.int 1) (by simp)

/-- `xs` largest first, by a comparison rather than by a key: the same reordering `sortDesc` performs,
and the place the two forms can be read against each other. -/
@[lgtm] private def sortDescBy as "sort-desc-by" (xs : list int) : list int :=
  sortBy xs (fun (a : int) (b : int) => b <= a)

#guard (sortDescBy.check {} []).isOk

-- The closure the comparison evaluates to captures the call's environment, the way a projection's
-- does, so the answers are computed over the two parameters of the `fun` rather than over `xs`.
example : FuncDecl.Apply sortDescBy {} [] [.list [.int 1, .int 2]] (.list [.int 2, .int 1]) := by
  have h :
    FuncDecl.Apply sortDescBy {} [] [.list [.int 1, .int 2]]
      (.list (Value.sortWith (fun x y => leValues y x) [.int 1, .int 2])) := by
    refine .EApply _ (.cons "xs" (hasType_intList (is := [1, 2])) .nil) ?_
    refine .EListSortBy (cmp := fun x y => leValues y x) _ _ (.EVarRef "xs" rfl) (.ELam _ _) ?_ ?_
    · rintro a ha b hb
      simp at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        exact .cons "a" (by constructor) (.cons "b" (by constructor) .nil)
    · rintro a ha b hb
      simp at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        exact .ELe _ _ (.EVarRef "b" rfl) (.EVarRef "a" rfl) (by simp [leValues])
  simpa [Value.sortWith, leValues] using h

-- Soundness covers the form, and what comes back is the element type: the comparison's result is a
-- `bool` and appears in no type the sort has.
example (vs : List Value) (v : Value) (h : FuncDecl.Apply sortDescBy {} [] [.list vs] v) :
    v.HasType {} (.list .int) :=
  h.hasType Globals.wellTyped_nil (by simp [sortDescBy, List.lookup])

-- So declaring the comparison's own type as the result type does not check, where the same body
-- under `map` would need exactly that.
#guard
  !(({ sortDescBy with resultType := [lgtm_ty| list bool] } : FuncDecl).check {} []).isOk

-- Only a list can be sorted, and only by a comparison of two of its elements answering with a
-- `bool`: a body comparing by one parameter is turned down, and so is one answering with an `int`.
example : ¬({ sortDescBy with body := [lgtm| sortBy n f] } : FuncDecl).WellTyped {} [] := by
  simp [sortDescBy, List.lookup]

example :
    ¬({ sortDescBy with body := [lgtm| sortBy xs (fun (a : int) => true)] } : FuncDecl).WellTyped {}
        [] := by
  simp [sortDescBy, List.lookup]

example :
    ¬({ sortDescBy with body := [lgtm| sortBy xs (fun (a : int) (b : int) => a + b)] } :
        FuncDecl).WellTyped {} [] := by
  simp [sortDescBy, List.lookup]

/-- What a sort by a comparison means, for every list rather than for one: the list it produces is as
long as the list it was given.

`sortDesc.length_of_eval` with `Value.length_sortWith` in place of `Value.length_sortByKey` — the
same fact about the same `mergeSort`, reached without the keys the other sort pairs the elements
with. -/
private theorem sortDescBy.length_of_eval {vs vs' : List Value}
    (h : Eval {} ⟨[("xs", .list vs)], []⟩
      [lgtm| sortBy xs (fun (a : int) (b : int) => b <= a)] (.list vs')) :
    vs.length = vs'.length := by
  cases h with
  | EListSortBy _ _ hl _ _ _ =>
      cases hl with
      | EVarRef _ hlx =>
          simp [Env.lookup, List.lookup] at hlx
          subst hlx
          simp

/-! A search is a call per element as a mapping is, and the same call: the element is the one
argument, `ArgsHaveType` holds it to the closure's parameter, and the body runs in the environment
the closure captured.  What the calls produce is a `bool`, as a comparison's do, and what comes back
out is neither a list nor an element but a position — `some(i)` for the first element the predicate
accepted, and the empty option where it accepted none.

Two rules, so the examples come in two kinds.  `pre ++ w :: post` is what the first one reads the
index off: the elements before the match are the ones the predicate turned down, and `post` is the
part no premise speaks of — the elements after the match are never handed to the predicate, which is
the short circuit and the one thing no other rule here has.

What can go wrong is what a mapping's two operands can, plus the one thing `sortBy` has: a predicate
that answers with something other than a `bool`. -/

-- An empty list finds nothing: there is no element for the predicate to be applied to, so both
-- premises over the elements are vacuous and the function is never entered.  It is the second rule
-- that fires — there is no element for the first to match.
example : Eval {} ∅ [lgtm| findIndex [ : int] (fun (x : int) => true)] (.option none) :=
  .EListFindIndexNone (vs := []) _ _ (.ENil _) (.ELam _ _) (by simp) (by simp)

-- A predicate the first element satisfies gives index 0, and the elements after it are never
-- reached: `post` is the rest of the list and nothing is said about it.
example :
    Eval {} ∅ [lgtm| findIndex [1, 2 : int] (fun (x : int) => x == 1)]
      (.option (some (.int 0))) :=
  .EListFindIndexSome (pre := []) (w := .int 1) (post := [.int 2]) _ _
    (.ECons _ _ (.EIntLit 1) (.ECons _ _ (.EIntLit 2) (.ENil _))) (.ELam _ _) (by simp) (by simp)
    (.cons "x" (.int 1) .nil)
    (.EEquals _ _ (.EVarRef "x" rfl) (.EIntLit 1) (by simp [Value.beq?]))

-- A later match is the same rule with the elements it turned down in `pre`, and how many there are
-- is the index: the call for each of them is what says the search went past it.
example :
    Eval {} ∅ [lgtm| findIndex [1, 2 : int] (fun (x : int) => x == 2)]
      (.option (some (.int 1))) :=
  .EListFindIndexSome (pre := [.int 1]) (w := .int 2) (post := []) _ _
    (.ECons _ _ (.EIntLit 1) (.ECons _ _ (.EIntLit 2) (.ENil _))) (.ELam _ _)
    (by rintro u hu
        simp at hu
        subst hu
        exact .cons "x" (.int 1) .nil)
    (by rintro u hu
        simp at hu
        subst hu
        exact .EEquals _ _ (.EVarRef "x" rfl) (.EIntLit 2) (by simp [Value.beq?]))
    (.cons "x" (.int 2) .nil)
    (.EEquals _ _ (.EVarRef "x" rfl) (.EIntLit 2) (by simp [Value.beq?]))

-- And a predicate no element satisfies is the second rule over a list that has elements: every one
-- of them answered `false`, which is what makes this the rule that speaks for the whole list.
example : Eval {} ∅ [lgtm| findIndex [1 : int] (fun (x : int) => x == 2)] (.option none) :=
  .EListFindIndexNone (vs := [.int 1]) _ _ (.ECons _ _ (.EIntLit 1) (.ENil _)) (.ELam _ _)
    (by rintro u hu
        simp at hu
        subst hu
        exact .cons "x" (.int 1) .nil)
    (by rintro u hu
        simp at hu
        subst hu
        exact .EEquals _ _ (.EVarRef "x" rfl) (.EIntLit 2) (by simp [Value.beq?]))

-- The short circuit, as a value where the other examples are shapes: the predicate has no value at
-- all on the second element — `unreachable` has no rule — and the search has one anyway, because the
-- first element matched and the second was never handed to it.  That is what `post` not appearing in
-- any premise buys, and no other form here has it.
example :
    Eval {} ∅
      [lgtm| findIndex [1, 2 : int]
        (fun (x : int) => if x == 1 then ( true ) else ( unreachable "never reached" : bool ))]
      (.option (some (.int 0))) :=
  .EListFindIndexSome (pre := []) (w := .int 1) (post := [.int 2]) _ _
    (.ECons _ _ (.EIntLit 1) (.ECons _ _ (.EIntLit 2) (.ENil _))) (.ELam _ _) (by simp) (by simp)
    (.cons "x" (.int 1) .nil)
    (.EIteTrue _ _ _ (.EEquals _ _ (.EVarRef "x" rfl) (.EIntLit 1) (by simp [Value.beq?]))
      (.EBoolLit true))

-- A second operand that is not a function leaves this stuck, exactly as it leaves a mapping stuck,
-- and it is both rules it leaves stuck: neither has a closure to call.
example (v : Value) : ¬Eval {} ∅ [lgtm| findIndex[ : int]1] v := by
  intro h
  cases h with
  | EListFindIndexSome _ _ _ hf _ _ _ _ => cases hf
  | EListFindIndexNone _ _ _ hf _ _ => cases hf

-- A predicate that does not answer with a `bool` is the thing that can go wrong here and nowhere
-- else, and it rules out both rules at once: the element can neither match nor be turned down, so
-- the search has no value.  That is exactly what the predicate's result type being held to `bool`
-- rules out.
example (v : Value) : ¬Eval {} ∅ [lgtm| findIndex [1 : int] (fun (x : int) => 0)] v := by
  intro h
  obtain ⟨vs, cb, cg, ps, body, hl, hf, hcase⟩ := h.listFindIndex_inv
  obtain rfl : vs = [.int 1] := by
    cases hl with
    | ECons _ _ h₁ h₂ =>
      cases h₁ with
      | EIntLit _ =>
        cases h₂ with
        | ENil _ => rfl
  cases hf with
  | ELam _ _ =>
    rcases hcase with ⟨pre, w, post, heq, -, hw, -⟩ | ⟨hall, -⟩
    · -- One element, so it is the match whichever way the list is split, and the call for it
      -- answered `0` where the rule needs `true`.
      obtain ⟨rfl, rfl⟩ : pre = [] ∧ w = .int 1 := by
        rcases pre with _ | ⟨u, pre'⟩ <;> simp_all
      cases hw
    · -- And the other rule needs the same call to have answered `false`.
      cases hall (.int 1) (by simp)

/-- Where `xs` first holds a zero, or nothing if it holds none. -/
@[lgtm] private def indexOfZero as "index-of-zero" (xs : list int) : option int :=
  findIndex xs (fun (x : int) => x == 0)

#guard (indexOfZero.check {} []).isOk

-- The closure the predicate evaluates to captures the call's environment, the way a mapping's does,
-- so the answers are computed over the parameter of the `fun` rather than over `xs`.
example : FuncDecl.Apply indexOfZero {} [] [.list [.int 1, .int 0]] (.option (some (.int 1))) :=
  .EApply _ (.cons "xs" (hasType_intList (is := [1, 0])) .nil)
    (.EListFindIndexSome (pre := [.int 1]) (w := .int 0) (post := []) _ _ (.EVarRef "xs" rfl)
      (.ELam _ _)
      (by rintro u hu
          simp at hu
          subst hu
          exact .cons "x" (.int 1) .nil)
      (by rintro u hu
          simp at hu
          subst hu
          exact .EEquals _ _ (.EVarRef "x" rfl) (.EIntLit 0) (by simp [Value.beq?]))
      (.cons "x" (.int 0) .nil)
      (.EEquals _ _ (.EVarRef "x" rfl) (.EIntLit 0) (by simp [Value.beq?])))

-- A list with no zero in it is the empty option, which is a value like any other: a search that
-- finds nothing is not stuck.
example : FuncDecl.Apply indexOfZero {} [] [.list [.int 1]] (.option none) :=
  .EApply _ (.cons "xs" (hasType_intList (is := [1])) .nil)
    (.EListFindIndexNone (vs := [.int 1]) _ _ (.EVarRef "xs" rfl) (.ELam _ _)
      (by rintro u hu
          simp at hu
          subst hu
          exact .cons "x" (.int 1) .nil)
      (by rintro u hu
          simp at hu
          subst hu
          exact .EEquals _ _ (.EVarRef "x" rfl) (.EIntLit 0) (by simp [Value.beq?])))

-- Soundness covers the form, and what comes back mentions neither the list's element type nor the
-- predicate's `bool`: an `option int` whatever the list held.
example (vs : List Value) (v : Value) (h : FuncDecl.Apply indexOfZero {} [] [.list vs] v) :
    v.HasType {} (.option .int) :=
  h.hasType Globals.wellTyped_nil (by simp [indexOfZero, List.lookup])

-- So declaring the element type as the result type does not check, where `sortOn` with the same
-- operands would need exactly that.
#guard !(({ indexOfZero with resultType := [lgtm_ty| list int] } : FuncDecl).check {} []).isOk

#guard !(({ indexOfZero with resultType := [lgtm_ty| int] } : FuncDecl).check {} []).isOk

-- Only a list can be searched, and only by a predicate of one of its elements answering with a
-- `bool`: a body searching an `int` parameter is turned down, and so is one whose predicate takes
-- two elements or answers with one.
example : ¬({ indexOfZero with body := [lgtm| findIndex n f] } : FuncDecl).WellTyped {} [] := by
  simp [indexOfZero, List.lookup]

example :
    ¬({ indexOfZero with
          body := [lgtm| findIndex xs (fun (a : int) (b : int) => a == b)] } :
        FuncDecl).WellTyped {} [] := by
  simp [indexOfZero, List.lookup]

example :
    ¬({ indexOfZero with body := [lgtm| findIndex xs (fun (x : int) => x)] } :
        FuncDecl).WellTyped {} [] := by
  simp [indexOfZero, List.lookup]

/-- What a search means, for every list rather than for one: the index it answers is a position the
list has.

The fact a proof about a searched list carries on with, and the one the form is for — an index
nothing bounds would be of no use to the `tupleGet`-shaped reads a caller makes.  Inverting the rule
leaves it as the length of the elements the predicate turned down, which is a position in
`pre ++ w :: post` because `w` is there. -/
private theorem indexOfZero.lt_length {vs : List Value} {i : Int}
    (h : Eval {} ⟨[("xs", .list vs)], []⟩
      [lgtm| findIndex xs (fun (x : int) => x == 0)] (.option (some (.int i)))) :
    i < vs.length := by
  obtain ⟨vs', _cb, _cg, _ps, _body, hl, -, hcase⟩ := h.listFindIndex_inv
  obtain rfl : vs' = vs := by
    cases hl with
    | EVarRef _ hlx =>
      simp [Env.lookup, List.lookup] at hlx
      exact hlx.symm
  rcases hcase with ⟨pre, w, post, rfl, -, -, heq⟩ | ⟨-, heq⟩
  · simp only [Value.option.injEq, Option.some.injEq, Value.int.injEq] at heq
    simp [← heq]
    omega
  · simp at heq

/-! An index evaluates the list and the position and hands back the option of what the list holds
there.  One rule, the way a get on a hashmap has one: `Value.index?` is a function of the two, so a
proof is left with the list, the position and what that said about them rather than with a case to
choose.  An index the list has no element at is not among the things that can go wrong — it is the
empty option, which is a value like any other.

So the examples come in one kind, and what separates them is what `Value.index?` answered.  Both
operands are always evaluated, as a comparison's two are, and there is no premise beyond them since
nothing is compared: a first operand that is not a list and a position that is not an `int` are the
only things that can go wrong, which is exactly what typing rules out. -/

-- A position the list has an element at is that element, in an option.
example : Eval {} ∅ [lgtm| [1, 2 : int][0]] (.option (some (.int 1))) :=
  .EListIndex _ _ (.ECons _ _ (.EIntLit 1) (.ECons _ _ (.EIntLit 2) (.ENil _))) (.EIntLit 0)

example : Eval {} ∅ [lgtm| [1, 2 : int][1]] (.option (some (.int 2))) :=
  .EListIndex _ _ (.ECons _ _ (.EIntLit 1) (.ECons _ _ (.EIntLit 2) (.ENil _))) (.EIntLit 1)

-- The position is an expression like any other and is evaluated whatever it took to arrive at it,
-- the way a comparison's operands are: neither operand is in a position to make the other
-- unnecessary.
example : Eval {} ∅ [lgtm| [1, 2 : int][0 + 1]] (.option (some (.int 2))) :=
  .EListIndex _ _ (.ECons _ _ (.EIntLit 1) (.ECons _ _ (.EIntLit 2) (.ENil _)))
    (.EPlus (n₁ := 0) (n₂ := 1) _ _ (.EIntLit 0) (.EIntLit 1))

-- A position past the end is the empty option rather than anything going wrong, which is the whole
-- of why the form has an option type — exactly as a key the map does not bind is for a get.
example : Eval {} ∅ [lgtm| [1, 2 : int][2]] (.option none) :=
  .EListIndex _ _ (.ECons _ _ (.EIntLit 1) (.ECons _ _ (.EIntLit 2) (.ENil _))) (.EIntLit 2)

-- An empty list holds nothing anywhere, so every position reads as empty out of one.
example : Eval {} ∅ [lgtm| [ : int][0]] (.option none) :=
  .EListIndex _ _ (.ENil _) (.EIntLit 0)

-- And a negative position is empty too.  `i.toNat` would read it as `0`, which is the one position
-- almost every list does have, so `Value.index?` turns it down before the lookup rather than after.
example : Eval {} ∅ [lgtm| [1, 2 : int][0 - 1]] (.option none) :=
  .EListIndex _ _ (.ECons _ _ (.EIntLit 1) (.ECons _ _ (.EIntLit 2) (.ENil _)))
    (.EMinus _ _ (.EIntLit 0) (.EIntLit 1))

-- A first operand that is not a list leaves this stuck, as a non-map leaves a get stuck.  It takes
-- the `Expression` to write rather than the surface syntax: brackets are read as an index only where
-- what they index is a list, and as a lookup everywhere else.
example (v : Value) : ¬Eval {} ∅ (Expression.listIndex (.intLit 1) (.intLit 0)) v := by
  intro h
  cases h with
  | EListIndex _ _ hl _ => cases hl

-- And a position that is not an `int` leaves it stuck, which is the other of the two: the lookup
-- reads a position, so a string in its place has no lookup at all.
example (v : Value) : ¬Eval {} ∅ [lgtm| [1 : int]["a"]] v := by
  intro h
  cases h with
  | EListIndex _ _ _ hi => cases hi

/-- The element of `xs` at `i`, and zero where there is none: the two halves of an index, which is
what an option result is for.  `getOr` over a hashmap further down is the same declaration written
in the same brackets, and the type of what is indexed is the whole of what tells them apart. -/
@[lgtm] private def elemOr as "elem-or" (xs : list int) (i : int) : int :=
  match xs[i] with | none => 0 | some(x) => x

#guard (elemOr.check {} []).isOk

-- The brackets over a `list int` parameter elaborated to an index rather than a lookup, which is
-- what makes the declaration check at all.
example : elemOr.body =
    Expression.optionMatch (.listIndex (.varRef "xs") (.varRef "i")) (.intLit 0) "x"
      (.varRef "x") :=
  rfl

-- Which case of the match runs is decided by what the index produced, so a position the list has
-- and one it does not are the two option rules, exactly as for any other option.
example : FuncDecl.Apply elemOr {} [] [.list [.int 1, .int 2], .int 1] (.int 2) :=
  .EApply _ (.cons "xs" (hasType_intList (is := [1, 2])) (.cons "i" (.int 1) .nil))
    (.EOptionMatchSome _ _ _ _
      (.EListIndex (vs := [.int 1, .int 2]) (n := 1) _ _ (.EVarRef "xs" rfl) (.EVarRef "i" rfl))
      (.EVarRef "x" rfl))

example : FuncDecl.Apply elemOr {} [] [.list [.int 1, .int 2], .int 5] (.int 0) :=
  .EApply _ (.cons "xs" (hasType_intList (is := [1, 2])) (.cons "i" (.int 5) .nil))
    (.EOptionMatchNone _ _ _ _
      (.EListIndex (vs := [.int 1, .int 2]) (n := 5) _ _ (.EVarRef "xs" rfl) (.EVarRef "i" rfl))
      (.EIntLit 0))

example : FuncDecl.Apply elemOr {} [] [.list [.int 1, .int 2], .int (-1)] (.int 0) :=
  .EApply _ (.cons "xs" (hasType_intList (is := [1, 2])) (.cons "i" (.int (-1)) .nil))
    (.EOptionMatchNone _ _ _ _
      (.EListIndex (vs := [.int 1, .int 2]) (n := -1) _ _ (.EVarRef "xs" rfl) (.EVarRef "i" rfl))
      (.EIntLit 0))

-- Soundness covers the form: the declared result type comes back whatever the list held and
-- whichever case the index fell in, which is what holding both cases of the match to one type was
-- for.
example (vs : List Value) (i : Int) (v : Value)
    (h : FuncDecl.Apply elemOr {} [] [.list vs, .int i] v) : v.HasType {} .int :=
  h.hasType Globals.wellTyped_nil (by simp [elemOr, List.lookup])

-- Only a list can be indexed, and only by an `int`: a body indexing the position by the list, or
-- the list by itself, is turned down.
example :
    ¬({ elemOr with body := Expression.listIndex (.varRef "i") (.varRef "xs") } :
        FuncDecl).WellTyped {} [] := by
  simp [elemOr, List.lookup]

-- And what an index produces is an option of the element type, not the element type: declaring the
-- result as the option is the one thing this body does not check at.
#guard
  !(({ elemOr with body := Expression.listIndex (.varRef "xs") (.varRef "i") } :
          FuncDecl).check
      {} []).isOk

#guard
  (({ elemOr with
            body := Expression.listIndex (.varRef "xs") (.varRef "i")
            resultType := [lgtm_ty| option int] } :
          FuncDecl).check
      {} []).isOk

/-- What an index means, for every list and position rather than for one: a lookup that produced a
value produced one the list holds.

This is the fact a proof about an indexed list carries on with, the way `getOr.mem_of_eval` is for a
get.  Inverting the rule leaves `Value.index?` saying so, and `Value.mem_of_index?` is what turns
that into membership — with no position in the statement, since a list is homogeneous and which
position it was found at says nothing more. -/
private theorem elemOr.mem_of_eval {vs : List Value} {i : Int} {w : Value}
    (h : Eval {} ⟨[("xs", .list vs), ("i", .int i)], []⟩
      (Expression.listIndex (.varRef "xs") (.varRef "i")) (.option (some w))) :
    w ∈ vs := by
  obtain ⟨vs', n, hl, hi, heq⟩ := h.listIndex_inv
  cases hl with
  | EVarRef _ hlx =>
    cases hi with
    | EVarRef _ hli =>
      simp only [Env.lookup, List.lookup] at hlx hli
      simp_all
      exact Value.mem_of_index? heq.symm

/-- The body of the inner lambda of `adderExpr`, `x + n`, which needs an `n` from outside itself. -/
private def adderInner : Expression :=
  [lgtm| x + n]

/-- A function that builds a function.  Spliced together from `adderInner` rather than written out
so that the two are the same term, which the closures below are stated in terms of. -/
private def adderExpr : Expression :=
  [lgtm| fun(n : int) => fun(x : int) => ~(adderInner)]

/-- The empty environment describes the empty context, which is all these examples need to say
about their environment. -/
private theorem hasType_nil : Env.HasType {} ∅ [] :=
  ⟨by simpa using Globals.wellTyped_nil, by simp, by simp⟩

-- Nothing in a lambda's body runs until it is applied; evaluating one only captures the
-- environment it was reached in.
example :
    Eval {} ∅ adderExpr ((∅ : Env).closure [("n", .int)] [lgtm| fun(x : int) => ~(adderInner)]) :=
  .ELam _ _

/-- Applying the outer lambda runs its body, which is itself a lambda, so what comes back is a
closure that has captured `n`. -/
private theorem eval_adder10 :
    Eval {} ∅ [lgtm| ~(adderExpr)(10)] (.closure [("n", .int 10)] [] [("x", .int)] adderInner) :=
  .EApp (vs := [.int 10]) _ _ (.ELam _ _) rfl
    (by
      rintro ⟨e, v⟩ hp; simp at hp; obtain ⟨rfl, rfl⟩ := hp; exact .EIntLit 10)
    (.cons "n" (.int 10) .nil) (.ELam _ _)

-- Applying that closure is what finally runs `x + n`, and it runs in the environment the closure
-- captured rather than the one the call was made from: `n` is in scope even though the caller's
-- environment is empty.
example : Eval {} ∅ [lgtm| ~(adderExpr)(10)(1)] (.int 11) :=
  .EApp (vs := [.int 1]) _ _ eval_adder10 rfl
    (by
      rintro ⟨e, v⟩ hp; simp at hp; obtain ⟨rfl, rfl⟩ := hp; exact .EIntLit 1)
    (.cons "x" (.int 1) .nil)
    (.EPlus (n₁ := 1) (n₂ := 10) _ _ (.EVarRef "x" rfl) (.EVarRef "n" rfl))

-- Soundness covers the new forms: a value of function type comes back, and which context the
-- closure captured is the theorem's business rather than the caller's.
example (v : Value) (h : Eval {} ∅ [lgtm| ~(adderExpr)(10)] v) : v.HasType {} (.fn [.int] .int) :=
  h.hasType hasType_nil (by simp [adderExpr, adderInner, List.lookup])

-- A call with the wrong number of arguments is stuck, just as it is for a declaration: the
-- parameters `ArgsHaveType` walks are the closure's own, so the lengths cannot disagree.
example (v : Value) : ¬Eval {} ∅ [lgtm| ~(adderExpr)(1, 2)] v := by
  intro h
  cases h with
  | EApp f args hf hlen hargs hat hbody =>
    simp only [adderExpr] at hf
    cases hf
    cases hat with
    | cons _ _ hrest =>
      cases hrest; simp at hlen

-- An argument of the wrong type is stuck too, so a closure cannot be entered with arguments its
-- parameters do not describe.
example (v : Value) : ¬Eval {} ∅ [lgtm| ~(adderExpr)("a")] v := by
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
example : Eval {} ∅ [lgtm| let x := 1 + 2; x + x] (.int 6) :=
  .ELet _ _ _ (.EPlus (n₁ := 1) (n₂ := 2) _ _ (.EIntLit 1) (.EIntLit 2))
    (.EPlus (n₁ := 3) (n₂ := 3) _ _ (.EVarRef "x" rfl) (.EVarRef "x" rfl))

-- Twice, so a later binding sees an earlier one.
example : Eval {} ∅ [lgtm| let x := 1; let y := x + 1; x + y] (.int 3) :=
  .ELet _ _ _ (.EIntLit 1)
    (.ELet _ _ _ (.EPlus (n₁ := 1) (n₂ := 1) _ _ (.EVarRef "x" rfl) (.EIntLit 1))
      (.EPlus (n₁ := 1) (n₂ := 2) _ _ (.EVarRef "x" rfl) (.EVarRef "y" rfl)))

/-- Twice one more than `n`. -/
@[lgtm] private def letDouble as"let-double"(n : int) : int := let m := n + 1; m + m

#guard (letDouble.check {} []).isOk

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
              | EVarRef _
                hlm' =>
                simp [letDouble, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
                  List.lookup] at hln hlm hlm'
                grind

-- A `let` whose body is a lambda is how a closure captures something other than a parameter: the
-- same closure `~(adderExpr)(10)` returns, reached without a call.
example :
    Eval {} ∅ [lgtm| let n := 10; fun(x : int) => ~(adderInner)]
      (.closure [("n", .int 10)] [] [("x", .int)] adderInner) :=
  .ELet _ _ _ (.EIntLit 10) (.ELam _ _)

-- The bound expression runs in the environment the `let` was reached in, so a `let` is not
-- recursive: `x` on the right of the `:=` is the outer `x`, and with no outer `x` it is stuck.
example : Eval {} ∅ [lgtm| let x := 1; let x := x + 1; x] (.int 2) :=
  .ELet _ _ _ (.EIntLit 1)
    (.ELet _ _ _ (.EPlus (n₁ := 1) (n₂ := 1) _ _ (.EVarRef "x" rfl) (.EIntLit 1))
      (.EVarRef "x" rfl))

example (v : Value) : ¬Eval {} ∅ [lgtm| let x := x + 1; x] v := by
  intro h
  cases h with
  | ELet _ _ _ hx _ =>
    cases hx with
    | EPlus _ _ h₁ _ =>
      cases h₁ with
      | EVarRef _ hlx => simp [Env.lookup] at hlx

/-- Build a function that adds `n` to its argument. -/
@[lgtm] private def adder(n : int) : (int) -> int := fun(m : int) => n + m

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
example : Eval {} ∅ [lgtm| true] (.bool true) :=
  .EBoolLit true

example : Eval {} ∅ [lgtm| false] (.bool false) :=
  .EBoolLit false

-- And to nothing else, which is what makes a literal condition decide the branch outright.
example : ¬Eval {} ∅ [lgtm| true] (.bool false) := by
  intro h; cases h

example : ¬Eval {} ∅ [lgtm| true] (.int 1) := by
  intro h; cases h

/-- `x` when `b`, and `y` otherwise. -/
@[lgtm] private def pick(b : bool)(x : int)(y : int) : int := if b then (x) else (y)

#guard (pick.check {} []).isOk

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
example (v : Value) : ¬FuncDecl.Apply pick {} [] [.int 0, .int 1, .int 2] v := by
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
      | EVarRef _
        hlx =>
        simp [pick, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup, List.lookup] at hlb hlx
        grind
  | EIteFalse _ _ _ hc hels =>
    cases hc with
    | EVarRef _ hlb =>
      cases hels with
      | EVarRef _
        hly =>
        simp [pick, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup, List.lookup] at hlb hly
        grind

-- The branch not taken is never evaluated, which is the whole of what a conditional does that a
-- two-argument function could not: the `else` below has no value at all, and the call still has one.
#guard !(({ pick with body := [lgtm| if b then (x) else (missing())] } : FuncDecl).check {} []).isOk

example :
    FuncDecl.Apply { pick with body := [lgtm| if b then (x) else (missing())] } {} []
      [.bool true, .int 1, .int 2] (.int 1) :=
  .EApply _ (.cons "b" (.bool true) (.cons "x" (.int 1) (.cons "y" (.int 2) .nil)))
    (.EIteTrue _ _ _ (.EVarRef "b" rfl) (.EVarRef "x" rfl))

/-- `xs` reversed when `b`, and as it came otherwise.  The branches are `list`s rather than `int`s,
which is what the form being polymorphic comes to: a conditional produces whatever they produce. -/
@[lgtm] private def maybeReverse as"maybe-reverse"(b : bool)(xs : list int) : list int :=
  if b then (reverse xs) else (xs)

#guard (maybeReverse.check {} []).isOk

example :
    FuncDecl.Apply maybeReverse {} [] [.bool true, .list [.int 1, .int 2]]
      (.list [.int 2, .int 1]) :=
  .EApply _ (.cons "b" (.bool true) (.cons "xs" (hasType_intList (is := [1, 2])) .nil))
    (.EIteTrue _ _ _ (.EVarRef "b" rfl)
      (.EListReverse (vs := [.int 1, .int 2]) _ (.EVarRef "xs" rfl)))

example :
    FuncDecl.Apply maybeReverse {} [] [.bool false, .list [.int 1, .int 2]]
      (.list [.int 1, .int 2]) :=
  .EApply _ (.cons "b" (.bool false) (.cons "xs" (hasType_intList (is := [1, 2])) .nil))
    (.EIteFalse _ _ _ (.EVarRef "b" rfl) (.EVarRef "xs" rfl))

example (v : Value) (b : Bool) (vs : List Value)
    (h : FuncDecl.Apply maybeReverse {} [] [.bool b, .list vs] v) : v.HasType {} (.list .int) :=
  h.hasType Globals.wellTyped_nil (by simp [maybeReverse, List.lookup])

/-- `x` when the condition is spelled out, which is `pick` with its own condition: a declaration of no
`bool` parameter that still runs a conditional. -/
@[lgtm] private def pickFirst as"pick-first"(x : int)(y : int) : int := if true then (x) else (y)

#guard (pickFirst.check {} []).isOk

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
    | EVarRef _
      hlx =>
      simp [pickFirst, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup] at hlx
      grind
  | EIteFalse _ _ _ hc _ => cases hc

example (v : Value) (x y : Int) (h : FuncDecl.Apply pickFirst {} [] [.int x, .int y] v) :
    v.HasType {} .int :=
  h.hasType Globals.wellTyped_nil (by simp [pickFirst, List.lookup])

/-- The literal on its own, which is the shortest declaration that returns a `bool`. -/
@[lgtm] private def yes : bool := true

#guard (yes.check {} []).isOk

example : FuncDecl.Apply yes {} [] [] (.bool true) :=
  .EApply _ .nil (.EBoolLit true)

-- Soundness covers the new form: the declared result type comes back from `yes` checking, which is
-- `Value.HasType.bool` reached through the catch-all case of `Eval.hasType` the other literals use.
example (v : Value) (h : FuncDecl.Apply yes {} [] [] v) : v.HasType {} .bool :=
  h.hasType Globals.wellTyped_nil (by simp [yes])

/-! The two boolean operators are the conditional again, with the operand that did not settle the
answer in the place of the branch that did not run: `EBoolAndFalse` and `EBoolOrTrue` mention their
second operand not at all, and the other two are the case where it is what the result came from.

What can go wrong is what a condition can: an operand that comes out something other than a `bool`
leaves this stuck, and that is exactly what typing rules out. -/

-- Which rule applies is decided by the first operand, and where that settles the answer the second
-- is never mentioned.
example : Eval {} ∅ [lgtm| false && true] (.bool false) :=
  .EBoolAndFalse _ _ (.EBoolLit false)

example : Eval {} ∅ [lgtm| true && false] (.bool false) :=
  .EBoolAndTrue _ _ (.EBoolLit true) (.EBoolLit false)

example : Eval {} ∅ [lgtm| true && true] (.bool true) :=
  .EBoolAndTrue _ _ (.EBoolLit true) (.EBoolLit true)

example : Eval {} ∅ [lgtm| true || false] (.bool true) :=
  .EBoolOrTrue _ _ (.EBoolLit true)

example : Eval {} ∅ [lgtm| false || true] (.bool true) :=
  .EBoolOrFalse _ _ (.EBoolLit false) (.EBoolLit true)

example : Eval {} ∅ [lgtm| false || false] (.bool false) :=
  .EBoolOrFalse _ _ (.EBoolLit false) (.EBoolLit false)

-- And to nothing else: a literal operand decides the rule outright, so the other value is one no
-- rule produces.
example : ¬Eval {} ∅ [lgtm| false && true] (.bool true) := by
  intro h
  cases h with
  | EBoolAndTrue _ _ hl _ => cases hl

example : ¬Eval {} ∅ [lgtm| true || false] (.bool false) := by
  intro h
  cases h with
  | EBoolOrFalse _ _ hl _ => cases hl

-- An operand that is not a `bool` leaves this stuck, which is the only thing that can go wrong
-- here: there is no truthiness, the way a conditional's condition has none.
example (v : Value) : ¬Eval {} ∅ [lgtm| 1 && true] v := by
  intro h
  cases h with
  | EBoolAndFalse _ _ hl => cases hl
  | EBoolAndTrue _ _ hl _ => cases hl

example (v : Value) : ¬Eval {} ∅ [lgtm| true && 1] v := by
  intro h
  cases h with
  | EBoolAndFalse _ _ hl => cases hl
  | EBoolAndTrue _ _ _ hr => cases hr

/-- Whether `b` and `c` both hold: the shortest declaration a conjunction is in. -/
@[lgtm] private def both(b : bool)(c : bool) : bool := b && c

#guard (both.check {} []).isOk

example : FuncDecl.Apply both {} [] [.bool false, .bool true] (.bool false) :=
  .EApply _ (.cons "b" (.bool false) (.cons "c" (.bool true) .nil))
    (.EBoolAndFalse _ _ (.EVarRef "b" rfl))

example : FuncDecl.Apply both {} [] [.bool true, .bool false] (.bool false) :=
  .EApply _ (.cons "b" (.bool true) (.cons "c" (.bool false) .nil))
    (.EBoolAndTrue _ _ (.EVarRef "b" rfl) (.EVarRef "c" rfl))

example : FuncDecl.Apply both {} [] [.bool true, .bool true] (.bool true) :=
  .EApply _ (.cons "b" (.bool true) (.cons "c" (.bool true) .nil))
    (.EBoolAndTrue _ _ (.EVarRef "b" rfl) (.EVarRef "c" rfl))

-- Soundness covers the form: a `bool` comes back whatever the operands came out, through the
-- catch-all case of `Eval.hasType` that `EEquals` and the literals go through.
example (v : Value) (b c : Bool) (h : FuncDecl.Apply both {} [] [.bool b, .bool c] v) :
    v.HasType {} .bool :=
  h.hasType Globals.wellTyped_nil (by simp [both, List.lookup])

-- An operand of any other type is stuck at the call, the way a conditional's condition is.
example (v : Value) : ¬FuncDecl.Apply both {} [] [.int 0, .bool true] v := by
  rintro ⟨-, hargs, -⟩
  cases hargs with
  | cons _ hv _ => cases hv

/-- What a conjunction means, for every pair of operands rather than for one: Lean's own `&&` of the
two values.

Inverting it is two cases rather than one because there are two rules, and the first of them never
heard of `c` — which is what makes this the fact short-circuiting has to be proved compatible with:
`false && c` is `false` in Lean whatever `c` is, and it is `false` here without `c` having a value
at all. -/
private theorem both.eq_and {b c : Bool} {res : Value}
    (h : FuncDecl.Apply both {} [] [.bool b, .bool c] res) : res = .bool (b && c) := by
  obtain ⟨-, -, hbody⟩ := h
  cases hbody with
  | EBoolAndFalse _ _ hl =>
    cases hl with
    | EVarRef _
      hlb =>
      simp [both, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup] at hlb
      grind
  | EBoolAndTrue _ _ hl hr =>
    cases hl with
    | EVarRef _ hlb =>
      cases hr with
      | EVarRef _
        hlc =>
        simp [both, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup, List.lookup] at hlb hlc
        grind

/-- Whether either of `b` and `c` holds, which is `both` with the values the two rules turn on
exchanged. -/
@[lgtm] private def either(b : bool)(c : bool) : bool := b || c

#guard (either.check {} []).isOk

example : FuncDecl.Apply either {} [] [.bool true, .bool false] (.bool true) :=
  .EApply _ (.cons "b" (.bool true) (.cons "c" (.bool false) .nil))
    (.EBoolOrTrue _ _ (.EVarRef "b" rfl))

example : FuncDecl.Apply either {} [] [.bool false, .bool true] (.bool true) :=
  .EApply _ (.cons "b" (.bool false) (.cons "c" (.bool true) .nil))
    (.EBoolOrFalse _ _ (.EVarRef "b" rfl) (.EVarRef "c" rfl))

example : FuncDecl.Apply either {} [] [.bool false, .bool false] (.bool false) :=
  .EApply _ (.cons "b" (.bool false) (.cons "c" (.bool false) .nil))
    (.EBoolOrFalse _ _ (.EVarRef "b" rfl) (.EVarRef "c" rfl))

private theorem either.eq_or {b c : Bool} {res : Value}
    (h : FuncDecl.Apply either {} [] [.bool b, .bool c] res) : res = .bool (b || c) := by
  obtain ⟨-, -, hbody⟩ := h
  cases hbody with
  | EBoolOrTrue _ _ hl =>
    cases hl with
    | EVarRef _
      hlb =>
      simp [either, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup] at hlb
      grind
  | EBoolOrFalse _ _ hl hr =>
    cases hl with
    | EVarRef _ hlb =>
      cases hr with
      | EVarRef _
        hlc =>
        simp [either, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup, List.lookup] at hlb hlc
        grind

-- The operand that did not settle the answer is never evaluated, which is what these forms do that
-- a two-argument function could not: the `missing()` below has no value at all, and the call still
-- has one — the same thing the branch of an `ite` that did not run demonstrates.
#guard !(({ both with body := [lgtm| b && missing()] } : FuncDecl).check {} []).isOk

example :
    FuncDecl.Apply { both with body := [lgtm| b && missing()] } {} [] [.bool false, .bool true]
      (.bool false) :=
  .EApply _ (.cons "b" (.bool false) (.cons "c" (.bool true) .nil))
    (.EBoolAndFalse _ _ (.EVarRef "b" rfl))

example :
    FuncDecl.Apply { either with body := [lgtm| b || missing()] } {} [] [.bool true, .bool false]
      (.bool true) :=
  .EApply _ (.cons "b" (.bool true) (.cons "c" (.bool false) .nil))
    (.EBoolOrTrue _ _ (.EVarRef "b" rfl))

-- And the operand that did settle it is evaluated, so a first operand with no value leaves the
-- whole of either form with none: `missing()` on the left is stuck under both rules.
example (v : Value) : ¬Eval {} ∅ [lgtm| missing() && true] v := by
  intro h
  cases h with
  | EBoolAndFalse _ _ hl =>
    cases hl with
    | EApp _ _ hf _ _ _ _ =>
      cases hf with
      | EVarRef _ hlf => simp [Env.lookup] at hlf
  | EBoolAndTrue _ _ hl _ =>
    cases hl with
    | EApp _ _ hf _ _ _ _ =>
      cases hf with
      | EVarRef _ hlf => simp [Env.lookup] at hlf

/-! ## Globals

Everything above ran with an empty table, so every name a body mentioned was one of its own
parameters.  These declare a table and call across it. -/

/-- Twice `n`. -/
@[lgtm] private def double(n : int) : int := n + n

/-- Four times `n`, which is `double` calling `double`. -/
@[lgtm] private def quad(n : int) : int := double(double(n))

/-- One more than twice `n`. -/
@[lgtm] private def doublePlus as"double-plus"(n : int) : int := double(n) + 1

/-- The answer.  A declaration of no parameters is how a global *variable* is written: its name has
type `() -> int`, so reading it is the call `answer()`. -/
@[lgtm] private def answer : int := 42

/-- One more than the answer, which is where the nullary global gets read. -/
@[lgtm] private def answerPlus as"answer-plus" : int := answer() + 1

private def arith : Globals :=
  Globals.ofDecls [double, quad, doublePlus, answer, answerPlus]

-- A body may mention a global, and `FuncDecl.check` finds it at the type its declaration gives.
#guard (quad.check {} arith).isOk

#guard (answerPlus.check {} arith).isOk

#guard (Globals.check {} arith).isOk

-- Without the table the same name is free, and the body does not check.  This is all `Globals` adds
-- to the checker: `double` has a type in `quad`'s body only because `arith` says so.
#guard !(quad.check {} []).isOk

#guard !(answerPlus.check {} []).isOk

-- The arity is the declaration's, so a global is as picky about how many arguments it gets as any
-- other function, and a nullary global has to be called rather than just named.
#guard !(({ quad with body := [lgtm| double(1, 2)] } : FuncDecl).check {} arith).isOk

#guard !(({ answerPlus with body := [lgtm| answer + 1] } : FuncDecl).check {} arith).isOk

-- A parameter shadows a global of the same name, in the checker and in `Env.lookup` alike.
#guard
  (({ quad with
            parameters := [("double", .int)], body := [lgtm| double] } :
          FuncDecl).check
      {} arith).isOk

#guard
  !(({ quad with
              parameters := [("double", .int)], body := [lgtm| double(1)] } :
            FuncDecl).check
        {} arith).isOk

-- A `let` shadows a global the same way a parameter does, so the name becomes a value rather than
-- something to call.
#guard (({ quad with body := [lgtm| let double := n; double] } : FuncDecl).check {} arith).isOk

#guard !(({ quad with body := [lgtm| let double := n; double(1)] } : FuncDecl).check {} arith).isOk

-- And `Env.lookup` reads it the same way round: the binding is found before the globals are
-- consulted, so the closure `double` would have resolved to is never built.
example :
    FuncDecl.Apply { quad with body := [lgtm| let double := n; double] } {} arith [.int 3]
      (.int 3) :=
  .EApply _ (.cons "n" (.int 3) .nil) (.ELet _ _ _ (.EVarRef "n" rfl) (.EVarRef "double" rfl))

-- A name that is neither a parameter nor a global is still free.
#guard !(({ double with body := [lgtm| missing(n)] } : FuncDecl).check {} arith).isOk

/-- Every declaration in `arith` checks, which is what a call to any of them needs. -/
private theorem arith.wellTyped : Globals.WellTyped {} arith := by
  refine Globals.wellTyped_of_forall fun p hp => ?_
  simp only [arith, Globals.ofDecls, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    simp [double, quad, doublePlus, answer, answerPlus, arith, Globals.ofDecls, FuncDecl.ty,
      List.lookup]

/-- A call across the table: `double` is not bound in `doublePlus`'s call environment, so
`Env.lookup` falls through to the globals and builds its closure there.

The body then runs in *that* closure's environment — `double`'s own parameter over the same globals
— and not in the one the call was made from. -/
private theorem eval_doublePlus : FuncDecl.Apply doublePlus {} arith [.int 3] (.int 7) :=
  .EApply _ (.cons "n" (.int 3) .nil)
    (.EPlus (n₁ := 6) (n₂ := 1) _ _
      (.EApp (vs := [.int 3]) _ _ (.EVarRef "double" rfl) rfl
        (by
          rintro ⟨e, v⟩ hp; simp at hp; obtain ⟨rfl, rfl⟩ := hp; exact .EVarRef "n" rfl)
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
@[lgtm] private def countdown(n : int) : int := countdown(n - 1)

#guard (Globals.check {} (Globals.ofDecls [countdown])).isOk

#guard !(countdown.check {} []).isOk

/-- Mutual recursion needs nothing further *of the type checker*: both are in the context both are
checked against.  What it does need is `@[lgtm, forward]`, since the command checking `ping` where
it is written has only the declarations before it, and `pong` is not one of them yet. -/
@[lgtm, forward] def pong(n : int) : int

@[lgtm] private def ping(n : int) : int := pong(n - 1)

@[lgtm] private def pong(n : int) : int := ping(n - 1)

#guard (Globals.check {} (Globals.ofDecls [ping, pong])).isOk

-- Neither checks alone, and neither checks with only itself in scope: it is the table that ties
-- them together.
#guard !(ping.check {} []).isOk

#guard !(ping.check {} (Globals.ofDecls [ping])).isOk

#guard !(Globals.check {} (Globals.ofDecls [ping])).isOk

/-! ## Programs

The same declarations again, read as a source file rather than as a table: `arith` is what
`arithProgram` presents to its own bodies. -/

private def arithProgram : Program :=
  { funcDecls := [double, quad, doublePlus, answer, answerPlus] }

example : arithProgram.globals = arith :=
  rfl

#guard (arithProgram.check).isOk

-- A program resolves the names its declarations declare, so `as` is what shows up here and the Lean
-- name does not.
example : arithProgram.lookup "double-plus" = some doublePlus :=
  rfl

example : arithProgram.lookup "doublePlus" = none :=
  rfl

example : arithProgram.lookup "missing" = none :=
  rfl

-- No two of them share a name, so none is shadowed and every one can be called.
example : arithProgram.NamesUnique := by decide

example : ¬({ funcDecls := [double, double] } : Program).NamesUnique := by decide

-- Which is what `lookup_self` is for: being one of the program's declarations is enough.
example : arithProgram.lookup quad.name = some quad :=
  arithProgram.lookup_self (by decide) (by simp [arithProgram])

-- A duplicate name is not unsound, just dead: the second declaration is checked and unreachable.
#guard (({ funcDecls := [double, { double with resultType := .int }] } : Program).check).isOk

example :
    ({ funcDecls := [answer, { answer with resultType := .string }] } : Program).lookup "answer" =
      some answer :=
  rfl

/-- `arithProgram` checks, which is a property of the program alone. -/
private theorem arithProgram.wellTyped : arithProgram.WellTyped :=
  arith.wellTyped

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
example (v : Value) : ¬arithProgram.Apply "missing" [.int 3] v := by
  rintro ⟨d, hd, -⟩
  rw [show arithProgram.lookup "missing" = none from rfl] at hd
  simp at hd

/-! ## Structs

A structure type is a top-level entity, so these examples carry a table of them the way the ones
above carry a table of declarations.  Evaluation never consults that table — the three struct rules
work on the value alone — so it shows up only where a type does: in `check`, in `Value.HasType`, and
in `ArgsHaveType`, which is why `Eval` carries it at all. -/

/-- A point in the plane. -/
@[lgtm] private structure Point where
  x : int
  y : int

private def points : TypeDecls :=
  { ss := Structs.ofDecls [Point] }

/-- A `Point` value has the type `Point` declares exactly when both its coordinates are `int`s.

Every `Value.HasType` for a struct comes down to a case analysis on the field name like this one: the
declaration and the value agree on which fields there are, and on each field they agree on the type.
Nothing here is about these particular coordinates, which is why one lemma covers every `Point`. -/
private theorem hasType_point {a b : Int} :
    Value.HasType points (.struct "Point" [("x", .int a), ("y", .int b)]) (.struct "Point") :=
  Value.hasType_struct_of_fields rfl rfl
    (by
      rintro p hp
      simp [Point] at hp
      rcases hp with rfl | rfl <;> exact .int _)

/-- Swap `p`'s coordinates. -/
@[lgtm] private def swap(p : struct Point) : struct Point := new Point{x = p.y, y = p.x}

#guard (swap.check points []).isOk

-- Without the struct table the body does not check: `new Point { … }` has nothing to check its
-- fields against, and the result type names nothing.  This is all `Structs` adds to the checker, and
-- it is the same thing `Globals` adds for names.
#guard !(swap.check {} []).isOk

/-- `EStructNew` evaluates one expression per field and keeps each result under that field's name, so
building a struct out of another one's fields is two `EStructGet`s under an `EStructNew`.

The globals are left open because nothing in this call reads one: `p` is a parameter, so `Env.lookup`
finds it in the bindings and never reaches the table. -/
private theorem eval_swap {gs : Globals} :
    FuncDecl.Apply swap points gs [.struct "Point" [("x", .int 1), ("y", .int 2)]]
      (.struct "Point" [("x", .int 2), ("y", .int 1)]) :=
  .EApply _ (.cons "p" hasType_point .nil)
    (.EStructNew _ _ rfl
      (by
        rintro p hp
        simp at hp
        rcases hp with rfl | rfl <;> exact .EStructGet _ _ (.EVarRef "p" rfl) rfl))

-- Soundness covers the new forms: what comes back has the declared struct type, and the reason is
-- that `swap` checks against `points` — nothing about this particular point.
example (v : Value)
    (h : FuncDecl.Apply swap points [] [.struct "Point" [("x", .int 1), ("y", .int 2)]] v) :
    v.HasType points (.struct "Point") :=
  h.hasType Globals.wellTyped_nil
    (by simp [swap, Point, points, List.lookup, Expression.fieldsComplete_eq_true] <;> grind)

/-- One more than `p`'s `x`, which is the field read on its own. -/
@[lgtm] private def getX as"get-x"(p : struct Point) : int := p.x + 1

#guard (getX.check points []).isOk

-- `EStructGet` reads the field out of the value, so it is the `EVarRef` that found the struct that
-- decides what comes back.
example : FuncDecl.Apply getX points [] [.struct "Point" [("x", .int 1), ("y", .int 2)]] (.int 2) :=
  .EApply _ (.cons "p" hasType_point .nil)
    (.EPlus (n₁ := 1) (n₂ := 1) _ _ (.EStructGet _ _ (.EVarRef "p" rfl) rfl) (.EIntLit 1))

-- A field the declaration does not list is not a field, so a body reading one does not check even
-- though the value it would be handed at run time carries only declared fields.
#guard !(({ getX with body := [lgtm| p.z + 1] } : FuncDecl).check points []).isOk

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
        | EIntLit
          _ =>
          simp [getX, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup] at hlp
          obtain ⟨rfl, rfl⟩ := hlp
          grind

/-- Move `p` along the x axis. -/
@[lgtm] private def shiftX as"shift-x"(p : struct Point)(d : int) : struct Point :=
  {p with x = p.x + d}

#guard (shiftX.check points []).isOk

-- An update rebinds the fields it names in place, so `y` comes through untouched and the fields stay
-- in the order `Point` declares them.
example :
    FuncDecl.Apply shiftX points [] [.struct "Point" [("x", .int 1), ("y", .int 2)], .int 10]
      (.struct "Point" [("x", .int 11), ("y", .int 2)]) := by
  refine .EApply _ (.cons "p" hasType_point (.cons "d" (.int 10) .nil)) ?_
  -- Both field lists have to be given: the result is `FieldValues.update fvs us`, and unification
  -- cannot read either of them back out of the value that comes out.
  refine
    .EStructUpdate (fvs := [("x", .int 1), ("y", .int 2)]) (us := [("x", .int 11)]) (.varRef "p")
      [("x", .plus (.structGet (.varRef "p") "x") (.varRef "d"))] ?_ rfl ?_
  · exact .EVarRef "p" rfl
  · rintro p hp
    simp at hp
    subst hp
    exact
      .EPlus (n₁ := 1) (n₂ := 10) _ _ (.EStructGet _ _ (.EVarRef "p" rfl) rfl) (.EVarRef "d" rfl)

-- An empty update is rejected, as `Expression.structUpdate` says it must be: it would be the
-- expression it updates, written so as to suggest otherwise.
#guard !(({ shiftX with body := [lgtm| {p with }] } : FuncDecl).check points []).isOk

-- And a field the declaration does not have cannot be introduced by one.
#guard !(({ shiftX with body := [lgtm| {p with z = d}] } : FuncDecl).check points []).isOk

/-- What an update leaves alone is the property it exists to express: `shift-x` moves `x` by `d` and
hands `y` back as it found it, for every point and every distance.

The update names one field, so `y` is a field it does not name — and `List.lookup_isSome_congr`,
applied to the premise that the expressions and the values share their field names, is what says an
update cannot reach a field it did not mention. -/
private theorem shiftX.eq_shifted {fvs : FieldValues} {a b d : Int} {res : Value}
    (hx : fvs.lookup "x" = some (.int a)) (hy : fvs.lookup "y" = some (.int b))
    (h : FuncDecl.Apply shiftX points [] [.struct "Point" fvs, .int d] res) :
    ∃ fvs',
      res = .struct "Point" fvs' ∧
        fvs'.lookup "x" = some (.int (a + d)) ∧ fvs'.lookup "y" = some (.int b) := by
  obtain ⟨-, -, hbody⟩ := h
  cases hbody with
  | @EStructUpdate _ _ _ us _ _ hp hnames hev =>
    cases hp with
    | EVarRef _
      hlp =>
      simp [shiftX, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup] at hlp
      obtain ⟨rfl, rfl⟩ := hlp
      refine ⟨_, rfl, ?_, ?_⟩
      · -- The one field the update names is `x`, and what it was given there is `p.x + d`.
        obtain ⟨w, hw⟩ : ∃ w, us.lookup "x" = some w :=
          Option.isSome_iff_exists.mp
            (by
              rw [← List.lookup_isSome_congr hnames "x"]; simp)
        have hev' :=
          hev _
            (List.mem_zip_of_lookup hnames (b := .plus (.structGet (.varRef "p") "x") (.varRef "d"))
              (by simp) hw)
        cases hev' with
        | EPlus _ _ h₁ h₂ =>
          cases h₁ with
          | EStructGet _ _ hq hfx =>
            cases hq with
            | EVarRef _ hlq =>
              cases h₂ with
              | EVarRef _
                hld =>
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

example : pointProgram.typeDecls = points :=
  rfl

#guard (pointProgram.check).isOk

-- The struct declaration is what makes it check: without it the three bodies mention a type that
-- names nothing.
#guard !(({ pointProgram with structDecls := [] } : Program).check).isOk

-- A program resolves the struct names it declares, and no two of them share a name — the counterpart
-- of `NamesUnique` for types rather than for declarations.
example : pointProgram.lookupStruct "Point" = some Point :=
  rfl

example : pointProgram.lookupStruct "Pair" = none :=
  rfl

example : pointProgram.StructNamesUnique := by decide

example : ¬({ pointProgram with structDecls := [Point, Point] } : Program).StructNamesUnique := by
  decide

-- Which is what `lookupStruct_self` is for: being one of the program's structure declarations is
-- enough to be the one its own name resolves to.
example : pointProgram.lookupStruct Point.name = some Point :=
  pointProgram.lookupStruct_self (by decide) (by simp [pointProgram])

-- No declaration of it names a field twice either, and this one `check` is about: the extra
-- declaration below is one no body mentions, so the three bodies check exactly as before and it is
-- the repeated field alone that turns the program down.
example : pointProgram.FieldNamesUnique := by decide

#guard
  !(({ pointProgram with
            structDecls := [Point, { name := "Dup", fields := [("x", .int), ("x", .string)] }] } :
          Program).check).isOk

#guard
  (({ pointProgram with structDecls := [Point, { name := "Dup", fields := [("x", .int)] }] } :
        Program).check).isOk

/-- `pointProgram` checks, which is a property of the program alone. -/
private theorem pointProgram.wellTyped : pointProgram.WellTyped := by
  refine Globals.wellTyped_of_forall fun p hp => ?_
  simp only [Program.globals, pointProgram, Globals.ofDecls, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    simp [swap, getX, shiftX, Point, Program.globals, Program.typeDecls, Program.structs,
      pointProgram, Globals.ofDecls, Structs.ofDecls, FuncDecl.ty, List.lookup,
      Expression.fieldsComplete_eq_true] <;>
    grind

-- Running it is calling one of its names, and soundness at the top covers a struct result type like
-- any other.
example :
    pointProgram.Apply "swap" [.struct "Point" [("x", .int 1), ("y", .int 2)]]
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
@[lgtm] private inductive Color where
  | Red
  | Green
  | Blue

/-- A shape, whose constructors carry what it takes to measure one. -/
@[lgtm] private inductive Shape where
  | Circle(int)
  | Rect(int, int)

private def shapes : TypeDecls :=
  { is := Inductives.ofDecls [Color, Shape] }

/-- A `Rect` has the type `Shape` declares exactly when both its sides are `int`s.

Every `Value.HasType` for an inductive value comes down to a walk along the zip like this one: the
constructor is looked up in the declaration, and what it carries is held to the types found there,
one for one.  Nothing here is about these particular sides, which is why one lemma covers every
`Rect`. -/
private theorem hasType_rect {w h : Int} :
    Value.HasType shapes (.ind "Shape" "Rect" [.int w, .int h]) (.ind "Shape") :=
  .ind rfl rfl rfl
    (by
      rintro p hp; simp at hp; rcases hp with rfl | rfl <;> exact .int _)

/-- A constructor carrying nothing has nothing to hold to a type, so the walk is empty. -/
private theorem hasType_red : Value.HasType shapes (.ind "Color" "Red" []) (.ind "Color") :=
  .ind rfl rfl rfl (by simp)

/-- How big `s` is, for a rough enough notion of size. -/
@[lgtm] private def area(s : inductive Shape) : int :=
  match s with | Circle(r) => r + r | Rect(w, h) => w + h

#guard (area.check shapes []).isOk

-- Without the inductive table the body does not check: the alternatives have no constructors to be
-- exhaustive over, and the parameter's type names nothing.  This is all `Inductives` adds to the
-- checker, and it is the same thing `Structs` adds for the other kind of type.
#guard !(area.check {} []).isOk

/-- The same function with its alternatives the other way round from the declaration's constructors.

An alternative says which constructor it is for, so this is the same function as `area`: it checks,
and `EIndMatch` finds the alternative for the value's constructor wherever in the match it was
written. -/
@[lgtm] private def areaSwapped as"area-swapped"(s : inductive Shape) : int :=
  match s with | Rect(w, h) => w + h | Circle(r) => r + r

#guard (areaSwapped.check shapes []).isOk

example : FuncDecl.Apply areaSwapped shapes [] [.ind "Shape" "Rect" [.int 3, .int 4]] (.int 7) :=
  .EApply _ (.cons "s" hasType_rect .nil)
    (.EIndMatch _ _ (.EVarRef "s" rfl) rfl
      (.EPlus (n₁ := 3) (n₂ := 4) _ _ (.EVarRef "w" rfl) (.EVarRef "h" rfl)))

example : FuncDecl.Apply areaSwapped shapes [] [.ind "Shape" "Circle" [.int 5]] (.int 10) :=
  .EApply _
    (.cons "s"
      (.ind rfl rfl rfl
        (by
          rintro p hp; simp at hp; subst hp; exact .int _))
      .nil)
    (.EIndMatch _ _ (.EVarRef "s" rfl) rfl
      (.EPlus (n₁ := 5) (n₂ := 5) _ _ (.EVarRef "r" rfl) (.EVarRef "r" rfl)))

-- Reordering is all the alternatives are free to do: a constructor left out is still not exhaustive,
-- and neither is one named twice in place of the one that is missing.
#guard
  !(({ areaSwapped with body := [lgtm| match s with | Rect(w, h) => w + h] } : FuncDecl).check
        shapes []).isOk

#guard
  !(({ areaSwapped with body := [lgtm| match s with | Rect(w, h) => w + h | Rect(w, h) => w] } :
            FuncDecl).check
        shapes []).isOk

/-- `EIndMatch` takes the alternative for the constructor the value carries and binds that
alternative's names to what the constructor holds, so a call comes down to the arithmetic in one
alternative and nothing at all in the others. -/
private theorem eval_area {gs : Globals} :
    FuncDecl.Apply area shapes gs [.ind "Shape" "Rect" [.int 3, .int 4]] (.int 7) :=
  .EApply _ (.cons "s" hasType_rect .nil)
    (.EIndMatch _ _ (.EVarRef "s" rfl) rfl
      (.EPlus (n₁ := 3) (n₂ := 4) _ _ (.EVarRef "w" rfl) (.EVarRef "h" rfl)))

-- The other alternative is chosen by the other constructor, and the names it binds are its own.
example : FuncDecl.Apply area shapes [] [.ind "Shape" "Circle" [.int 5]] (.int 10) :=
  .EApply _
    (.cons "s"
      (.ind rfl rfl rfl
        (by
          rintro p hp; simp at hp; subst hp; exact .int _))
      .nil)
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
    | EVarRef _
      hls =>
      simp [area, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup] at hls
      obtain ⟨rfl, rfl, rfl⟩ := hls
      simp [List.lookup] at halt
      obtain ⟨rfl, rfl⟩ := halt
      cases hb with
      | EPlus _ _ h₁ h₂ =>
        cases h₁ with
        | EVarRef _ hlw =>
          cases h₂ with
          | EVarRef _
            hlh =>
            simp [area, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
              List.lookup] at hlw hlh
            grind

/-- A square of side `n`, which is the other half: a constructor applied to values. -/
@[lgtm] private def square(n : int) : inductive Shape := new Shape.Rect(n, n)

#guard (square.check shapes []).isOk

-- `EIndNew` evaluates one expression per thing the constructor carries and keeps the values in that
-- order, under the two names it was given.
example : FuncDecl.Apply square shapes [] [.int 2] (.ind "Shape" "Rect" [.int 2, .int 2]) :=
  .EApply _ (.cons "n" (.int 2) .nil)
    (.EIndNew (vs := [.int 2, .int 2]) _ _ _ rfl
      (by
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
@[lgtm] private inductive Tree where
  | Leaf
  | Node(inductive Tree, int, inductive Tree)

private def trees : TypeDecls :=
  { is := Inductives.ofDecls [Tree] }

/-- The sum of `t`'s labels. -/
@[lgtm] private def total(t : inductive Tree) : int :=
  match t with | Leaf => 0 | Node(l, n, r) => total(l) + n + total(r)

private def forest : Globals :=
  Globals.ofDecls [total]

-- The declaration checks against a context holding itself, exactly as `countdown` does: it is the
-- table that makes the recursive call resolve, and the recursive *type* needs nothing at all, since
-- `Tree` is resolved where it is mentioned rather than where it was declared.
#guard (Globals.check trees forest).isOk

#guard !(total.check trees []).isOk

/-- `Leaf` carries nothing, so the empty alternative runs and the recursion stops. -/
private theorem hasType_leaf : Value.HasType trees (.ind "Tree" "Leaf" []) (.ind "Tree") :=
  .ind rfl rfl rfl (by simp)

example : FuncDecl.Apply total trees forest [.ind "Tree" "Leaf" []] (.int 0) :=
  .EApply _ (.cons "t" hasType_leaf .nil) (.EIndMatch _ _ (.EVarRef "t" rfl) rfl (.EIntLit 0))

/-- A `Node` has the type `Tree` declares when its label is an `int` and its two subtrees have it
too, which is the recursive case of the same walk `hasType_leaf` ends. -/
private theorem hasType_node {l r : Value} {n : Int} (hl : Value.HasType trees l (.ind "Tree"))
    (hr : Value.HasType trees r (.ind "Tree")) :
    Value.HasType trees (.ind "Tree" "Node" [l, .int n, r]) (.ind "Tree") :=
  .ind rfl rfl rfl
    (by
      rintro p hp
      simp at hp
      rcases hp with rfl | rfl | rfl
      · exact hl
      · exact .int _
      · exact hr)

/-! ### A program with inductive types

The same declarations again, read as a source file: a `Program` carries its inductive types beside
its structure types and its declarations, and `Program.typeDecls` is the bundle its bodies are
checked and run against. -/

private def shapeProgram : Program where
  funcDecls := [area, square]
  inductiveDecls := [Color, Shape]

example : shapeProgram.typeDecls = shapes :=
  rfl

#guard (shapeProgram.check).isOk

-- The type declarations are what make it check: without them both bodies mention a type that names
-- nothing.
#guard !(({ shapeProgram with inductiveDecls := [] } : Program).check).isOk

-- A program resolves the inductive names it declares, and no two of them share a name — the
-- counterpart of `StructNamesUnique` for the other kind of type.
example : shapeProgram.lookupInductive "Shape" = some Shape :=
  rfl

example : shapeProgram.lookupInductive "Hue" = none :=
  rfl

example : shapeProgram.InductiveNamesUnique := by decide

example :
    ¬({ shapeProgram with inductiveDecls := [Color, Color] } : Program).InductiveNamesUnique := by
  decide

example : shapeProgram.lookupInductive Shape.name = some Shape :=
  shapeProgram.lookupInductive_self (by decide) (by simp [shapeProgram])

-- And no declaration of the program names a constructor twice, which is the condition inside a
-- declaration rather than across them: it is what makes `Shape`'s every constructor reachable, and
-- what keeps a match on it from having to write an alternative that can never run.
example : shapeProgram.CtorNamesUnique := by decide

example :
    ¬({ shapeProgram with
            inductiveDecls :=
              [{ name := "Shape", constructors := [("Circle", [.int]), ("Circle", [])] }] } :
          Program).CtorNamesUnique := by
  decide

-- `check` is where that is enforced, as it is for a repeated field: the extra type below is one no
-- body mentions, so what turns the program down is the repeated constructor and nothing else.
#guard
  !(({ shapeProgram with
            inductiveDecls :=
              [Color, Shape, { name := "Dup", constructors := [("Red", []), ("Red", [.int])] }] } :
          Program).check).isOk

#guard
  (({ shapeProgram with
          inductiveDecls :=
            [Color, Shape,
              { name := "Dup", constructors := [("Red", []), ("Crimson", [.int])] }] } :
        Program).check).isOk

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

/-! ## Equality

`EEquals` evaluates both operands and hands back what `Value.beq?` made of the two values.  What is
new here is a rule whose result is computed from the values rather than copied out of one of them, so
these examples come in two kinds: the `rfl` that says what a particular comparison came to, and the
theorems that say what a comparison coming out `true` or `false` *means* — which is
`Value.equiv_of_beq?` and `Value.ne_of_beq?`, and which is the whole reason the form is worth having
in a proof. -/

-- A comparison of literals is decided by the values they evaluate to, and nothing about the type
-- compared survives into the result: a `bool` comes back from `int`s, `string`s and `bool`s alike.
example : Eval {} ∅ [lgtm| 1 == 1] (.bool true) :=
  .EEquals _ _ (.EIntLit 1) (.EIntLit 1) rfl

example : Eval {} ∅ [lgtm| 1 == 2] (.bool false) :=
  .EEquals _ _ (.EIntLit 1) (.EIntLit 2) rfl

example : Eval {} ∅ [lgtm| "a" == "a"] (.bool true) :=
  .EEquals _ _ (.EStringLit "a") (.EStringLit "a") rfl

example : Eval {} ∅ [lgtm| "a" == "b"] (.bool false) :=
  .EEquals _ _ (.EStringLit "a") (.EStringLit "b") rfl

example : Eval {} ∅ [lgtm| true == false] (.bool false) :=
  .EEquals _ _ (.EBoolLit true) (.EBoolLit false) rfl

-- A comparison is decided by the values and not by the expressions: these two sides are different
-- expressions that compute the same `int`.
example : Eval {} ∅ [lgtm| 1 + 2 == 5 - 2] (.bool true) :=
  .EEquals _ _ (.EPlus (n₁ := 1) (n₂ := 2) _ _ (.EIntLit 1) (.EIntLit 2))
    (.EMinus (n₁ := 5) (n₂ := 2) _ _ (.EIntLit 5) (.EIntLit 2)) rfl

-- Lists are compared element by element, and two of different lengths are different without the
-- elements coming into it.
example : Eval {} ∅ [lgtm| [1, 2 : int] == [1, 2 : int]] (.bool true) :=
  .EEquals _ _ (.ECons _ _ (.EIntLit 1) (.ECons _ _ (.EIntLit 2) (.ENil .int)))
    (.ECons _ _ (.EIntLit 1) (.ECons _ _ (.EIntLit 2) (.ENil .int))) rfl

example : Eval {} ∅ [lgtm| [1, 2 : int] == [1, 3 : int]] (.bool false) :=
  .EEquals _ _ (.ECons _ _ (.EIntLit 1) (.ECons _ _ (.EIntLit 2) (.ENil .int)))
    (.ECons _ _ (.EIntLit 1) (.ECons _ _ (.EIntLit 3) (.ENil .int))) rfl

example : Eval {} ∅ [lgtm| [1 : int] == [ : int]] (.bool false) :=
  .EEquals _ _ (.ECons _ _ (.EIntLit 1) (.ENil .int)) (.ENil .int) rfl

/-- Whether `x` and `y` are the same. -/
@[lgtm] private def same(x : int)(y : int) : bool := x == y

#guard (same.check {} []).isOk

example : FuncDecl.Apply same {} [] [.int 1, .int 1] (.bool true) :=
  .EApply _ (.cons "x" (.int 1) (.cons "y" (.int 1) .nil))
    (.EEquals _ _ (.EVarRef "x" rfl) (.EVarRef "y" rfl) rfl)

example : FuncDecl.Apply same {} [] [.int 1, .int 2] (.bool false) :=
  .EApply _ (.cons "x" (.int 1) (.cons "y" (.int 2) .nil))
    (.EEquals _ _ (.EVarRef "x" rfl) (.EVarRef "y" rfl) rfl)

-- Soundness covers the new form: a `bool` comes back because the body is a comparison, which is the
-- one thing its type says — the type the operands shared is not part of it.
example (v : Value) (x y : Int) (h : FuncDecl.Apply same {} [] [.int x, .int y] v) :
    v.HasType {} .bool :=
  h.hasType Globals.wellTyped_nil (by simp [same, List.lookup])

/-- What a comparison computes, for every pair of `int`s rather than for one: inverting `EEquals`
down to the two `EVarRef`s leaves `Value.beq?` on the values the parameters were bound to, which on
`int`s is their own equality. -/
private theorem same.eq_beq {x y : Int} {res : Value}
    (h : FuncDecl.Apply same {} [] [.int x, .int y] res) : res = .bool (x == y) := by
  obtain ⟨-, -, hbody⟩ := h
  cases hbody with
  | EEquals _ _ h₁ h₂ hb =>
    cases h₁ with
    | EVarRef _ hlx =>
      cases h₂ with
      | EVarRef _
        hly =>
        simp [same, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup, List.lookup] at hlx hly
        subst hlx
        subst hly
        simp [Value.beq?] at hb
        grind

/-! ### What a comparison means

The examples above are about particular values.  These are the general facts: a comparison that came
out `true` is the two values being *equal*, and one that came out `false` is them being unequal.
Neither is about the type compared, which is what makes one proof of each cover every comparison a
declaration performs. -/

/-- Whether two trees are the same tree.  A recursive type is comparable — each value of one is
finite, however deep the type is — so this is a declaration about a type a comparison has to walk all
the way down. -/
@[lgtm] private def sameTree as"same-tree"(a : inductive Tree)(b : inductive Tree) : bool := a == b

#guard (sameTree.check trees []).isOk

-- The same constructors all the way down, carrying the same data, is what `true` comes from.
example :
    FuncDecl.Apply sameTree trees [] [.ind "Tree" "Leaf" [], .ind "Tree" "Leaf" []] (.bool true) :=
  .EApply _ (.cons "a" hasType_leaf (.cons "b" hasType_leaf .nil))
    (.EEquals _ _ (.EVarRef "a" rfl) (.EVarRef "b" rfl) rfl)

-- A difference in the constructor is a difference in the value, and it is decided without the data
-- either of them carries being compared at all.
example :
    FuncDecl.Apply sameTree trees []
      [.ind "Tree" "Node" [.ind "Tree" "Leaf" [], .int 1, .ind "Tree" "Leaf" []],
        .ind "Tree" "Leaf" []]
      (.bool false) :=
  .EApply _ (.cons "a" (hasType_node hasType_leaf hasType_leaf) (.cons "b" hasType_leaf .nil))
    (.EEquals _ _ (.EVarRef "a" rfl) (.EVarRef "b" rfl) rfl)

-- A recursive type is comparable, so soundness covers `sameTree` too: the walk `Ty.comparable` does
-- over `Tree`'s own constructors is what `decide` settles here.
example (a b v : Value) (h : FuncDecl.Apply sameTree trees [] [a, b] v) : v.HasType trees .bool :=
  h.hasType Globals.wellTyped_nil
    (by
      simp [sameTree, List.lookup]; decide)

/-- A comparison that came out `true` is the two values being equivalent — for any two of them, and
whatever `Tree`s they were.

This is what the form is for.  `EEquals` hands back what `Value.beq?` said, and
`Value.beq?_eq_some_iff` is what says that answer was the right one, so a `true` reached through a
comparison is `Value.Equiv` for the rest of the proof to work with — which is Lean's own `=` at
every position but a struct's fields, and a `Tree` carries none. -/
private theorem sameTree.equiv_of_true {a b : Value}
    (h : FuncDecl.Apply sameTree trees [] [a, b] (.bool true)) : Value.Equiv a b := by
  obtain ⟨-, -, hbody⟩ := h
  cases hbody with
  | EEquals _ _ h₁ h₂ hb =>
    cases h₁ with
    | EVarRef _ hla =>
      cases h₂ with
      | EVarRef _
        hlb =>
        simp [sameTree, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
          List.lookup] at hla hlb
        subst hla
        subst hlb
        exact Value.equiv_of_beq? hb

/-- And one that came out `false` is them being unequal — Lean's own `≠`, which is the half of the
fact that matching a struct's fields by name costs nothing: two values a comparison separated are
different values however either of them carries its fields. -/
private theorem sameTree.ne_of_false {a b : Value}
    (h : FuncDecl.Apply sameTree trees [] [a, b] (.bool false)) : a ≠ b := by
  obtain ⟨-, -, hbody⟩ := h
  cases hbody with
  | EEquals _ _ h₁ h₂ hb =>
    cases h₁ with
    | EVarRef _ hla =>
      cases h₂ with
      | EVarRef _
        hlb =>
        simp [sameTree, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
          List.lookup] at hla hlb
        subst hla
        subst hlb
        exact Value.ne_of_beq? hb

/-! ### Structs

A struct value is a name and an association list, so comparing two of them is comparing what their
fields hold, name for name — whichever order either of them carries its fields in, since a
`structNew` may write the declaration's fields in any order and the value keeps the order it was
written in. -/

/-- Whether two points are the same point. -/
@[lgtm] private def samePoint as"same-point"(p : struct Point)(q : struct Point) : bool := p == q

#guard (samePoint.check points []).isOk

example :
    FuncDecl.Apply samePoint points []
      [.struct "Point" [("x", .int 1), ("y", .int 2)],
        .struct "Point" [("x", .int 1), ("y", .int 2)]]
      (.bool true) :=
  .EApply _ (.cons "p" hasType_point (.cons "q" hasType_point .nil))
    (.EEquals _ _ (.EVarRef "p" rfl) (.EVarRef "q" rfl) rfl)

example :
    FuncDecl.Apply samePoint points []
      [.struct "Point" [("x", .int 1), ("y", .int 2)],
        .struct "Point" [("x", .int 1), ("y", .int 3)]]
      (.bool false) :=
  .EApply _ (.cons "p" hasType_point (.cons "q" hasType_point .nil))
    (.EEquals _ _ (.EVarRef "p" rfl) (.EVarRef "q" rfl) rfl)

-- Soundness covers a comparison of structs like any other: what comes back is a `bool`, and the
-- part of `samePoint` checking that the other declarations do not have is `Ty.comparable` on
-- `Point` — one comparison on the table this program wrote out, which is what `decide` is for.
example (vp vq v : Value) (h : FuncDecl.Apply samePoint points [] [vp, vq] v) :
    v.HasType points .bool :=
  h.hasType Globals.wellTyped_nil
    (by
      simp [samePoint, List.lookup]; decide)

-- The same point written the other way round is the same point: the fields are matched by the names
-- they were written under, so which order either value was built in decides nothing.  Compared
-- positionally this pair had no comparison at all — two well-typed values with no value for the
-- comparison, which `Value.beqFields?` matching by name is what fixed.
example :
    Eval points ∅
      (Expression.equals (.structNew "Point" [("x", .intLit 1), ("y", .intLit 2)])
        (.structNew "Point" [("y", .intLit 2), ("x", .intLit 1)]))
      (.bool true) :=
  .EEquals (v₁ := .struct "Point" [("x", .int 1), ("y", .int 2)])
    (v₂ := .struct "Point" [("y", .int 2), ("x", .int 1)]) _ _
    (.EStructNew _ _ rfl
      (by
        rintro p hp
        simp at hp
        rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact .EIntLit _))
    (.EStructNew _ _ rfl
      (by
        rintro p hp
        simp at hp
        rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact .EIntLit _))
    rfl

-- What a `false` takes is a field holding a different value, not a field written somewhere else.
-- Fields that disagree on *which* names there are get `false` as well, which is a pair typing rules
-- out rather than one the comparison has nothing to say about.
example :
    Value.beq? (.struct "Point" [("x", .int 1), ("y", .int 2)])
        (.struct "Point" [("y", .int 3), ("x", .int 1)]) = some false :=
  rfl

example :
    Value.beq? (.struct "Point" [("x", .int 1)]) (.struct "Point" [("z", .int 1)]) = some false :=
  rfl

-- An update is what makes two points of one declaration differ, so this is the comparison deciding
-- something about a value that was computed rather than passed in.
example :
    FuncDecl.Apply { samePoint with body := [lgtm| p == {q with x = 1}] } points []
      [.struct "Point" [("x", .int 1), ("y", .int 2)],
        .struct "Point" [("x", .int 9), ("y", .int 2)]]
      (.bool true) :=
  .EApply _ (.cons "p" hasType_point (.cons "q" hasType_point .nil))
    (.EEquals _ _ (.EVarRef "p" rfl)
      (.EStructUpdate (us := [("x", .int 1)]) _ _ (.EVarRef "q" rfl) rfl
        (by
          rintro ⟨e, v⟩ hp
          simp at hp
          obtain ⟨rfl, rfl⟩ := hp
          exact .EIntLit 1))
      rfl)

/-! ### What cannot be compared

A closure is the one value `Value.beq?` has no answer for, so a comparison of two of them is stuck:
it has no value at all, rather than a wrong one.  `Ty.comparable` is the type checker's side of this,
and it is why the declarations above never meet the case. -/

-- The comparison of two functions has no value, and it makes no difference that these two closures
-- came from the same `lam`: two functions are the same function when they agree on every argument,
-- which is not something either value carries.
example (v : Value) : ¬Eval {} ∅ [lgtm| (fun(x : int) => x) == (fun(x : int) => x)] v := by
  intro h
  cases h with
  | EEquals _ _ h₁ h₂ hb =>
    cases h₁
    cases h₂
    simp [Env.closure, Value.beq?] at hb

/-- `same` with both of its parameters of function type, which is the declaration the type checker
has to turn down. -/
private def sameFns : FuncDecl :=
  { same with
    parameters := [("g", .fn [.int] .int), ("h", .fn [.int] .int)]
    body := [lgtm| g == h] }

-- And it does turn it down, so the stuck case is one a well-typed program never reaches: it is
-- `Ty.comparable` that rules it out, on the type the two operands share.
#guard !(sameFns.check {} []).isOk

/-! ## Ordering

`ELt` and `ELe` evaluate both operands and hand back what `Value.lt?` and `Value.le?` made of the
two values, which is `EEquals` with another comparison in place of `Value.beq?`.  The two forms are
one comparison read two ways, so what is worth showing of each is where they differ: the pair of
equal values, and nothing else. -/

-- A comparison of literals is decided by the values they evaluate to, and what comes out is a
-- `bool` whatever was compared.
example : Eval {} ∅ [lgtm| 1 < 2] (.bool true) :=
  .ELt _ _ (.EIntLit 1) (.EIntLit 2) rfl

example : Eval {} ∅ [lgtm| 2 < 1] (.bool false) :=
  .ELt _ _ (.EIntLit 2) (.EIntLit 1) rfl

example : Eval {} ∅ [lgtm| "a" < "b"] (.bool true) :=
  .ELt _ _ (.EStringLit "a") (.EStringLit "b") rfl

example : Eval {} ∅ [lgtm| "b" < "a"] (.bool false) :=
  .ELt _ _ (.EStringLit "b") (.EStringLit "a") rfl

-- Two equal values are the one pair the two forms disagree about, which is the whole of what
-- separates them.
example : Eval {} ∅ [lgtm| 1 < 1] (.bool false) :=
  .ELt _ _ (.EIntLit 1) (.EIntLit 1) rfl

example : Eval {} ∅ [lgtm| 1 <= 1] (.bool true) :=
  .ELe _ _ (.EIntLit 1) (.EIntLit 1) rfl

example : Eval {} ∅ [lgtm| 2 <= 1] (.bool false) :=
  .ELe _ _ (.EIntLit 2) (.EIntLit 1) rfl

example : Eval {} ∅ [lgtm| "a" <= "a"] (.bool true) :=
  .ELe _ _ (.EStringLit "a") (.EStringLit "a") rfl

-- A comparison is decided by the values and not by the expressions, as a `==` is.
example : Eval {} ∅ [lgtm| 1 + 1 < 5 - 2] (.bool true) :=
  .ELt _ _ (.EPlus (n₁ := 1) (n₂ := 1) _ _ (.EIntLit 1) (.EIntLit 1))
    (.EMinus (n₁ := 5) (n₂ := 2) _ _ (.EIntLit 5) (.EIntLit 2)) rfl

-- Lists are compared lexicographically: the first position the two disagree at decides them, and
-- the elements past it are not compared at all.
example : Eval {} ∅ [lgtm| [1, 2 : int] < [1, 3 : int]] (.bool true) :=
  .ELt _ _ (.ECons _ _ (.EIntLit 1) (.ECons _ _ (.EIntLit 2) (.ENil .int)))
    (.ECons _ _ (.EIntLit 1) (.ECons _ _ (.EIntLit 3) (.ENil .int))) rfl

example : Eval {} ∅ [lgtm| [2, 0 : int] < [1, 9 : int]] (.bool false) :=
  .ELt _ _ (.ECons _ _ (.EIntLit 2) (.ECons _ _ (.EIntLit 0) (.ENil .int)))
    (.ECons _ _ (.EIntLit 1) (.ECons _ _ (.EIntLit 9) (.ENil .int))) rfl

-- A list that runs out first comes before one that has not, which is the one answer the elements
-- do not come into — and the empty list is below every other.
example : Eval {} ∅ [lgtm| [1 : int] < [1, 0 : int]] (.bool true) :=
  .ELt _ _ (.ECons _ _ (.EIntLit 1) (.ENil .int))
    (.ECons _ _ (.EIntLit 1) (.ECons _ _ (.EIntLit 0) (.ENil .int))) rfl

example : Eval {} ∅ [lgtm| [ : int] <= [1 : int]] (.bool true) :=
  .ELe _ _ (.ENil .int) (.ECons _ _ (.EIntLit 1) (.ENil .int)) rfl

example : Eval {} ∅ [lgtm| [ : int] <= [ : int]] (.bool true) :=
  .ELe _ _ (.ENil .int) (.ENil .int) rfl

-- An empty option comes before one that holds a value, and two that hold values are their values
-- compared.
example : Eval {} ∅ (Expression.lt (.optionNone .int) (.optionSome (.intLit 0))) (.bool true) :=
  .ELt _ _ (.ENone .int) (.ESome _ (.EIntLit 0)) rfl

example : Eval {} ∅ (Expression.lt (.optionSome (.intLit 0)) (.optionNone .int)) (.bool false) :=
  .ELt _ _ (.ESome _ (.EIntLit 0)) (.ENone .int) rfl

example :
    Eval {} ∅ (Expression.lt (.optionSome (.intLit 1)) (.optionSome (.intLit 2))) (.bool true) :=
  .ELt _ _ (.ESome _ (.EIntLit 1)) (.ESome _ (.EIntLit 2)) rfl

example : Eval {} ∅ (Expression.le (.optionNone .int) (.optionNone .int)) (.bool true) :=
  .ELe _ _ (.ENone .int) (.ENone .int) rfl

-- A tuple is compared by the same walk a list is, position by position, so a pair agreeing on its
-- first position is decided by its second.
example : Eval {} ∅ [lgtm| tuple("a", 1) < tuple("a", 2)] (.bool true) :=
  .ELt _ _
    (.ETupleNew (vs := [.string "a", .int 1]) _ rfl
      (by
        rintro p hp
        simp at hp
        rcases hp with rfl | rfl
        · exact .EStringLit "a"
        · exact .EIntLit 1))
    (.ETupleNew (vs := [.string "a", .int 2]) _ rfl
      (by
        rintro p hp
        simp at hp
        rcases hp with rfl | rfl
        · exact .EStringLit "a"
        · exact .EIntLit 2))
    rfl

/-- Whether `x` is below `y`. -/
@[lgtm] private def below(x : int)(y : int) : bool := x < y

/-- Whether `x` is below `y` or is `y`. -/
@[lgtm] private def atMost as"at-most"(x : int)(y : int) : bool := x <= y

#guard (below.check {} []).isOk

#guard (atMost.check {} []).isOk

example : FuncDecl.Apply below {} [] [.int 1, .int 2] (.bool true) :=
  .EApply _ (.cons "x" (.int 1) (.cons "y" (.int 2) .nil))
    (.ELt _ _ (.EVarRef "x" rfl) (.EVarRef "y" rfl) rfl)

example : FuncDecl.Apply below {} [] [.int 2, .int 2] (.bool false) :=
  .EApply _ (.cons "x" (.int 2) (.cons "y" (.int 2) .nil))
    (.ELt _ _ (.EVarRef "x" rfl) (.EVarRef "y" rfl) rfl)

example : FuncDecl.Apply atMost {} [] [.int 2, .int 2] (.bool true) :=
  .EApply _ (.cons "x" (.int 2) (.cons "y" (.int 2) .nil))
    (.ELe _ _ (.EVarRef "x" rfl) (.EVarRef "y" rfl) rfl)

-- Soundness covers the new forms: a `bool` comes back because the body is a comparison, which is
-- the one thing its type says — the type the operands shared is not part of it.
example (v : Value) (x y : Int) (h : FuncDecl.Apply below {} [] [.int x, .int y] v) :
    v.HasType {} .bool :=
  h.hasType Globals.wellTyped_nil (by simp [below, List.lookup])

/-! ### What an ordering means

The examples above are about particular values.  These are the general facts: what a comparison of
two `int`s came out as *is* Lean's own `<` and `≤` on them, which is what `Value.lt?_int` and
`Value.le?_int` say and what the rest of a proof carries on with. -/

/-- What `below` computes, for every pair of `int`s rather than for one: inverting `ELt` down to the
two `EVarRef`s leaves `Value.lt?` on the values the parameters were bound to, which on `int`s is
their own `<`. -/
private theorem below.eq_lt {x y : Int} {res : Value}
    (h : FuncDecl.Apply below {} [] [.int x, .int y] res) : res = .bool (decide (x < y)) := by
  obtain ⟨-, -, hbody⟩ := h
  cases hbody with
  | ELt _ _ h₁ h₂ hb =>
    cases h₁ with
    | EVarRef _ hlx =>
      cases h₂ with
      | EVarRef _
        hly =>
        simp [below, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup, List.lookup] at hlx hly
        subst hlx
        subst hly
        simp at hb
        grind

/-- And `atMost` the same with `≤`, which is the one pair of values the two forms differ on read as
a fact about every pair. -/
private theorem atMost.eq_le {x y : Int} {res : Value}
    (h : FuncDecl.Apply atMost {} [] [.int x, .int y] res) : res = .bool (decide (x ≤ y)) := by
  obtain ⟨-, -, hbody⟩ := h
  cases hbody with
  | ELe _ _ h₁ h₂ hb =>
    cases h₁ with
    | EVarRef _ hlx =>
      cases h₂ with
      | EVarRef _
        hly =>
        simp [atMost, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup, List.lookup] at hlx hly
        subst hlx
        subst hly
        simp at hb
        grind

-- Which is enough to reason about a call without mentioning the relation again.
example {x y : Int} {res : Value} (hxy : x < y)
    (h : FuncDecl.Apply below {} [] [.int x, .int y] res) : res = .bool true := by
  simp [below.eq_lt h, hxy]

/-! ### What cannot be ordered

An ordering gives up on more values than an equality does: a `bool`, a hashmap, a struct value and a
value of an inductive type all have no ordering here, where all four can be compared for equality.
`Ty.orderable` is the type checker's side of it, and it is why a well-typed program never meets one
of these. -/

-- Two `bool`s have no ordering, so this is stuck even though the same two compare for equality
-- perfectly well.
example (v : Value) : ¬Eval {} ∅ [lgtm| true < false] v := by
  intro h
  cases h with
  | ELt _ _ h₁ h₂ hb =>
    cases h₁
    cases h₂
    simp [Value.lt?, Value.cmp?] at hb

example : Eval {} ∅ [lgtm| true == false] (.bool false) :=
  .EEquals _ _ (.EBoolLit true) (.EBoolLit false) rfl

-- And two struct values have none either, for a reason of the same kind: a declaration's fields are
-- named rather than ordered, so there is nothing to say which of them to look at first.
example (v : Value) :
    ¬Eval {} ⟨[("p", .struct "Point" [("x", .int 1), ("y", .int 2)])], []⟩ [lgtm| p < p] v := by
  intro h
  cases h with
  | ELt _ _ h₁ h₂ hb =>
    cases h₁ with
    | EVarRef _ hlp =>
      cases h₂ with
      | EVarRef _ hlp' =>
        simp [Env.lookup, List.lookup] at hlp hlp'
        subst hlp
        subst hlp'
        simp [Value.lt?, Value.cmp?] at hb

/-- `below` with both of its parameters of a type that has no ordering, which is the declaration the
type checker has to turn down. -/
private def belowBools : FuncDecl :=
  { below with parameters := [("x", .bool), ("y", .bool)] }

/-- The same over a struct type, which is the other kind of operand an equality would have taken. -/
private def belowPoints : FuncDecl :=
  { below with parameters := [("x", .struct "Point"), ("y", .struct "Point")] }

-- And it does turn them down, so the stuck cases above are ones a well-typed program never reaches.
#guard !(belowBools.check {} []).isOk

#guard !(belowPoints.check points []).isOk

/-! ### The ordering read as a value

`min` and `max` are the other two things to do with an ordering: a comparison answers `bool` for
whatever it compared, where these hand back one of the operands and so are given the one type they
can be — `int`, and `Int`'s own `min` and `max` are what they come out as. -/

-- Both operands are evaluated and the smaller or the larger of the two is the value, whichever side
-- it was written on.
example : Eval {} ∅ [lgtm| min 1 2] (.int 1) :=
  .EMin _ _ (.EIntLit 1) (.EIntLit 2)

example : Eval {} ∅ [lgtm| min 2 1] (.int 1) :=
  .EMin _ _ (.EIntLit 2) (.EIntLit 1)

example : Eval {} ∅ [lgtm| max 1 2] (.int 2) :=
  .EMax _ _ (.EIntLit 1) (.EIntLit 2)

example : Eval {} ∅ [lgtm| max 2 1] (.int 2) :=
  .EMax _ _ (.EIntLit 2) (.EIntLit 1)

-- Two equal operands are the one pair the two forms agree on, which is the opposite of how `<` and
-- `<=` differ there.
example : Eval {} ∅ [lgtm| min 1 1] (.int 1) :=
  .EMin _ _ (.EIntLit 1) (.EIntLit 1)

example : Eval {} ∅ [lgtm| max 1 1] (.int 1) :=
  .EMax _ _ (.EIntLit 1) (.EIntLit 1)

-- The operands are expressions like any others, so what is compared is what they evaluated to.
example : Eval {} ∅ [lgtm| min (1 + 1) (5 - 2)] (.int 2) :=
  .EMin _ _ (.EPlus (n₁ := 1) (n₂ := 1) _ _ (.EIntLit 1) (.EIntLit 1))
    (.EMinus (n₁ := 5) (n₂ := 2) _ _ (.EIntLit 5) (.EIntLit 2))

example : Eval {} ∅ [lgtm| max (min 1 2) 3] (.int 3) :=
  .EMax _ _ (.EMin _ _ (.EIntLit 1) (.EIntLit 2)) (.EIntLit 3)

-- Nothing but an `int` is accepted on either side, so a `string` operand is stuck where a `<` of
-- two `string`s is not.
example : Eval {} ∅ [lgtm| "a" < "b"] (.bool true) :=
  .ELt _ _ (.EStringLit "a") (.EStringLit "b") rfl

example (v : Value) : ¬Eval {} ∅ [lgtm| min "a" "b"] v := by
  intro h
  cases h with
  | EMin _ _ h₁ _ => cases h₁

example (v : Value) : ¬Eval {} ∅ [lgtm| max 1 "b"] v := by
  intro h
  cases h with
  | EMax _ _ _ h₂ => cases h₂

/-- Clamp `x` up to `lo` and down to `hi`. -/
@[lgtm] private def clamp(x : int)(lo : int)(hi : int) : int := min (max x lo) hi

#guard (clamp.check {} []).isOk

example : FuncDecl.Apply clamp {} [] [.int 7, .int 0, .int 5] (.int 5) :=
  .EApply _ (.cons "x" (.int 7) (.cons "lo" (.int 0) (.cons "hi" (.int 5) .nil)))
    (.EMin (n₁ := max 7 0) (n₂ := 5) _ _
      (.EMax (n₁ := 7) (n₂ := 0) _ _ (.EVarRef "x" rfl) (.EVarRef "lo" rfl)) (.EVarRef "hi" rfl))

example : FuncDecl.Apply clamp {} [] [.int (-3), .int 0, .int 5] (.int 0) :=
  .EApply _ (.cons "x" (.int (-3)) (.cons "lo" (.int 0) (.cons "hi" (.int 5) .nil)))
    (.EMin (n₁ := max (-3) 0) (n₂ := 5) _ _
      (.EMax (n₁ := -3) (n₂ := 0) _ _ (.EVarRef "x" rfl) (.EVarRef "lo" rfl)) (.EVarRef "hi" rfl))

-- Soundness covers the new forms: an `int` comes back because the body is a minimum, which is all
-- its type says.
example (v : Value) (x lo hi : Int) (h : FuncDecl.Apply clamp {} [] [.int x, .int lo, .int hi] v) :
    v.HasType {} .int :=
  h.hasType Globals.wellTyped_nil (by simp [clamp, List.lookup])

/-- What `clamp` computes, for every triple of `int`s rather than for one: inverting the two rules
down to the `EVarRef`s leaves `Int`'s own `min` and `max` on the values the parameters were bound
to, which is what the rest of a proof carries on with. -/
private theorem clamp.eq_min_max {x lo hi : Int} {res : Value}
    (h : FuncDecl.Apply clamp {} [] [.int x, .int lo, .int hi] res) :
    res = .int (min (max x lo) hi) := by
  obtain ⟨-, -, hbody⟩ := h
  cases hbody with
  | EMin _ _ h₁ h₂ =>
    cases h₂ with
    | EVarRef _ hlhi =>
      cases h₁ with
      | EMax _ _ h₃ h₄ =>
        cases h₃ with
        | EVarRef _ hlx =>
          cases h₄ with
          | EVarRef _
            hllo =>
            simp [clamp, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
              List.lookup] at hlx hllo hlhi
            grind

-- Which is enough to reason about a call without mentioning the relation again.
example {x lo hi : Int} {res : Value} (hx : lo ≤ x) (hxhi : x ≤ hi)
    (h : FuncDecl.Apply clamp {} [] [.int x, .int lo, .int hi] res) : res = .int x := by
  simp [clamp.eq_min_max h, Int.max_eq_left hx, Int.min_eq_left hxhi]

/-! ## Options

The option forms are the two values and the match between them.  There is no table here, the way
there is for the struct and inductive sections: an `option` carries its element type rather than
naming a declaration, so nothing about one is resolved anywhere.

They have no surface syntax yet, so the expressions are spliced in with `~(...)`: the DSL is what
`@[lgtm] def` is written in, and a form it does not cover is still an ordinary `Expression`. -/

-- An empty option evaluates to the empty value, and its annotation goes nowhere: a value carries no
-- type, so the two below produce the same value and it is only the type checker that tells them
-- apart.
example : Eval {} ∅ (Expression.optionNone .int) (.option none) :=
  .ENone .int

example : Eval {} ∅ (Expression.optionNone .string) (.option none) :=
  .ENone .string

-- And to nothing else, so an empty option is not an empty list.
example : ¬Eval {} ∅ (Expression.optionNone .int) (.list []) := by
  intro h; cases h

-- A `some` evaluates what it holds and keeps the value, whatever it took to arrive at.
example : Eval {} ∅ (Expression.optionSome (.intLit 1)) (.option (some (.int 1))) :=
  .ESome _ (.EIntLit 1)

example :
    Eval {} ∅ (Expression.optionSome (.plus (.intLit 1) (.intLit 2))) (.option (some (.int 3))) :=
  .ESome _ (.EPlus (n₁ := 1) (n₂ := 2) _ _ (.EIntLit 1) (.EIntLit 2))

example :
    Eval {} ∅ (Expression.optionSome (.optionSome (.intLit 1)))
      (.option (some (.option (some (.int 1))))) :=
  .ESome _ (.ESome _ (.EIntLit 1))

/-- An option holding an `int` has the type `option int`, which is the whole of what
`Value.HasType` asks of one: the value it holds is held to the type the option gives. -/
private theorem hasType_someInt {a : Int} :
    Value.HasType td (.option (some (.int a))) (.option .int) :=
  .optionSome (.int a)

/-- An empty one has that type too, and it has every other option type as well — there is no value
in it for a type to be required of, the way there is none in an empty list. -/
private theorem hasType_noneInt : Value.HasType td (.option none) (.option .int) :=
  .optionNone

example : Value.HasType ({} : TypeDecls) (.option none) (.option (.fn [.int] .int)) :=
  .optionNone

/-- One more than what `o` holds, and `0` when it holds nothing. -/
@[lgtm] private def succOr as"succ-or"(o : ~(Ty.option .int)) : int :=
  ~(Expression.optionMatch (.varRef "o") (.intLit 0) "x" [lgtm| x + 1])

#guard (succOr.check {} []).isOk

-- Which case runs is decided by the value the scrutinee produced, and it is `EOptionMatchSome` or
-- `EOptionMatchNone` that says so — the two rules `ite` has two of for the same reason.
example : FuncDecl.Apply succOr {} [] [.option (some (.int 4))] (.int 5) :=
  .EApply _ (.cons "o" hasType_someInt .nil)
    (.EOptionMatchSome _ _ _ _ (.EVarRef "o" rfl)
      (.EPlus (n₁ := 4) (n₂ := 1) _ _ (.EVarRef "x" rfl) (.EIntLit 1)))

example : FuncDecl.Apply succOr {} [] [.option none] (.int 0) :=
  .EApply _ (.cons "o" hasType_noneInt .nil)
    (.EOptionMatchNone _ _ _ _ (.EVarRef "o" rfl) (.EIntLit 0))

-- Soundness covers the new forms: the declared result type comes back from `succOr` checking, with
-- nothing said about which case ran — which is the reason both cases were held to one type.
example (v : Value) (ov : Option Value) (h : FuncDecl.Apply succOr {} [] [.option ov] v) :
    v.HasType {} .int :=
  h.hasType Globals.wellTyped_nil (by simp [succOr, List.lookup])

-- An argument of the wrong type is stuck at the call, as it is for any other parameter: an option of
-- `int`s is what the declaration asks for, and an `int` is not one.
example (v : Value) : ¬FuncDecl.Apply succOr {} [] [.int 4] v := by
  rintro ⟨-, hargs, -⟩
  cases hargs with
  | cons _ hv _ => cases hv

/-- Which case runs is decided by the value and nothing else, and the one that runs computes with
what the option held: this is the property a match exists to express, for every `a` rather than for
one.

Inverting it is two cases because there are two rules, and the `none` rule is ruled out by the value
the scrutinee produced rather than assumed away — an option holding a value is not an empty one, and
that is all it takes. -/
private theorem succOr.eq_succ {a : Int} {res : Value}
    (h : FuncDecl.Apply succOr {} [] [.option (some (.int a))] res) : res = .int (a + 1) := by
  obtain ⟨-, -, hbody⟩ := h
  cases hbody with
  | EOptionMatchNone _ _ _ _ hsc _ =>
    cases hsc with
    | EVarRef _ hlo => simp [succOr, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup] at hlo
  | EOptionMatchSome _ _ _ _ hsc hsb =>
    cases hsc with
    | EVarRef _
      hlo =>
      simp [succOr, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup] at hlo
      subst hlo
      cases hsb with
      | EPlus _ _ h₁ h₂ =>
        cases h₁ with
        | EVarRef _ hlx =>
          cases h₂ with
          | EIntLit _ =>
            -- The name the `some` case bound is read straight off the front of the bindings, so
            -- nothing about the call environment comes into it.
            simp [Env.lookup, List.lookup] at hlx
            grind

/-- And the other case for an empty option, which is the half that computes with nothing at all. -/
private theorem succOr.eq_zero {res : Value} (h : FuncDecl.Apply succOr {} [] [.option none] res) :
    res = .int 0 := by
  obtain ⟨-, -, hbody⟩ := h
  cases hbody with
  | EOptionMatchNone _ _ _ _ hsc hnb =>
    cases hnb with
    | EIntLit _ => rfl
  | EOptionMatchSome _ _ _ _ hsc _ =>
    cases hsc with
    | EVarRef _ hlo => simp [succOr, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup] at hlo

-- The case that did not run is never evaluated, the way the branch of an `ite` that did not is: the
-- `none` case below has no value at all, and the match still has one.
example :
    Eval {} ∅
      (Expression.optionMatch (.optionSome (.intLit 1)) (.app (.varRef "missing") []) "x"
        (.varRef "x"))
      (.int 1) :=
  .EOptionMatchSome _ _ _ _ (.ESome _ (.EIntLit 1)) (.EVarRef "x" rfl)

-- The name is bound in front of the environment, so it shadows what was there, and only inside its
-- own case.
example :
    Eval {} ⟨[("x", .int 9)], []⟩
      (Expression.optionMatch (.optionSome (.intLit 1)) (.varRef "x") "x" (.varRef "x")) (.int 1) :=
  .EOptionMatchSome _ _ _ _ (.ESome _ (.EIntLit 1)) (.EVarRef "x" rfl)

example :
    Eval {} ⟨[("x", .int 9)], []⟩
      (Expression.optionMatch (.optionNone .int) (.varRef "x") "x" (.varRef "x")) (.int 9) :=
  .EOptionMatchNone _ _ _ _ (.ENone .int) (.EVarRef "x" rfl)

-- A match on a value that is not an option is stuck: neither rule applies, which is exactly what
-- the scrutinee having to be an option rules out.  Unlike `EIndMatch`, there is nothing else that
-- can get one stuck — the two cases are the two an option value comes in, so none has to be found.
example (v : Value) :
    ¬Eval {} ∅ (Expression.optionMatch (.intLit 1) (.intLit 0) "x" (.varRef "x")) v := by
  intro h
  cases h with
  | EOptionMatchNone _ _ _ _ hsc _ => cases hsc
  | EOptionMatchSome _ _ _ _ hsc _ => cases hsc

/-- `n`, held in an option, which is the other half: a value put into one rather than taken out. -/
@[lgtm] private def justIt as"just-it"(n : int) : ~(Ty.option .int) :=
  ~(Expression.optionSome [lgtm| n])

#guard (justIt.check {} []).isOk

example : FuncDecl.Apply justIt {} [] [.int 7] (.option (some (.int 7))) :=
  .EApply _ (.cons "n" (.int 7) .nil) (.ESome _ (.EVarRef "n" rfl))

example (v : Value) (a : Int) (h : FuncDecl.Apply justIt {} [] [.int a] v) :
    v.HasType {} (.option .int) :=
  h.hasType Globals.wellTyped_nil (by simp [justIt, List.lookup])

/-- Nothing, at `int`: the shortest declaration that returns an option, and the one place the
annotation is all there is to go on. -/
@[lgtm] private def nothing : ~(Ty.option .int) := ~(Expression.optionNone .int)

#guard (nothing.check {} []).isOk

example : FuncDecl.Apply nothing {} [] [] (.option none) :=
  .EApply _ .nil (.ENone .int)

-- The value an empty option evaluates to says nothing about the type, so it is the declaration that
-- does: soundness gives back `option int` because `nothing` says `option int`.
example (v : Value) (h : FuncDecl.Apply nothing {} [] [] v) : v.HasType {} (.option .int) :=
  h.hasType Globals.wellTyped_nil (by simp [nothing])

/-! ### Comparing options

`Value.beq?` compares two options by comparing what they hold, and decides an empty one against a
full one without looking at the value — the same way it decides two lists of different lengths. -/

example :
    Eval {} ∅ (Expression.equals (.optionSome (.intLit 1)) (.optionSome (.intLit 1)))
      (.bool true) :=
  .EEquals _ _ (.ESome _ (.EIntLit 1)) (.ESome _ (.EIntLit 1)) rfl

example :
    Eval {} ∅ (Expression.equals (.optionSome (.intLit 1)) (.optionSome (.intLit 2)))
      (.bool false) :=
  .EEquals _ _ (.ESome _ (.EIntLit 1)) (.ESome _ (.EIntLit 2)) rfl

example : Eval {} ∅ (Expression.equals (.optionNone .int) (.optionNone .int)) (.bool true) :=
  .EEquals _ _ (.ENone .int) (.ENone .int) rfl

example :
    Eval {} ∅ (Expression.equals (.optionSome (.intLit 1)) (.optionNone .int)) (.bool false) :=
  .EEquals _ _ (.ESome _ (.EIntLit 1)) (.ENone .int) rfl

/-- Whether two options hold the same thing. -/
private def sameOpt : FuncDecl where
  docstring := "Whether `a` and `b` are the same."
  name := "same-opt"
  parameters := [("a", .option .int), ("b", .option .int)]
  body := .equals (.varRef "a") (.varRef "b")
  resultType := .bool

#guard (sameOpt.check {} []).isOk

-- And what a comparison coming out `true` *means* holds for options like any other comparable type:
-- it is the two values being equivalent, which is what `Value.beq?_eq_some_iff` is for.
private theorem sameOpt.equiv_of_true {a b : Value}
    (h : FuncDecl.Apply sameOpt {} [] [a, b] (.bool true)) : Value.Equiv a b := by
  obtain ⟨-, -, hbody⟩ := h
  cases hbody with
  | EEquals _ _ h₁ h₂ hb =>
    cases h₁ with
    | EVarRef _ hla =>
      cases h₂ with
      | EVarRef _
        hlb =>
        simp [sameOpt, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup,
          List.lookup] at hla hlb
        subst hla
        subst hlb
        exact Value.equiv_of_beq? hb

-- An option of function type is the one option there is no comparing, so a comparison of two of
-- them is stuck — and `Ty.comparable` is what keeps a well-typed program from reaching it.
example (v : Value) :
    ¬Eval {} ∅
        (Expression.equals (.optionSome (.lam [("x", .int)] (.varRef "x")))
          (.optionSome (.lam [("x", .int)] (.varRef "x"))))
        v := by
  intro h
  cases h with
  | EEquals _ _ h₁ h₂ hb =>
    cases h₁ with
    | ESome _ hl =>
      cases h₂ with
      | ESome _ hr =>
        cases hl
        cases hr
        simp [Env.closure, Value.beq?] at hb

#guard
  !(({ sameOpt with
              parameters := [("a", .option (.fn [.int] .int)), ("b", .option (.fn [.int] .int))] } :
            FuncDecl).check
        {} []).isOk

/-! ## Hashmaps

A hashmap value is the bindings it carries, as an association list: one pair per key, each key
beside the value it is bound to.  There is no table here, the way there is none in the option
section: a hashmap type relates two types rather than naming a declaration, so nothing about one is
resolved anywhere.

What is new is that reading and rebinding a map both *compare* values.  `KeyValues.lookup?` and
`KeyValues.erase?` run `Value.beq?` along the keys, so both are partial exactly where a comparison
is, and both appear as a premise the way `EEquals`'s comparison does — discharged by `rfl` below,
since the keys are literals. -/

-- An empty map binds nothing, and its two annotations go nowhere: a value carries no type, so the
-- two below produce the same value and it is only the type checker that tells them apart.
example : Eval {} ∅ [lgtm| hashmap(string, int)] (.hashmap []) :=
  .EHashmapEmpty .string .int

example : Eval {} ∅ [lgtm| hashmap(int, string)] (.hashmap []) :=
  .EHashmapEmpty .int .string

-- And to nothing else, so an empty map is not an empty list.
example : ¬Eval {} ∅ [lgtm| hashmap(string, int)] (.list []) := by
  intro h; cases h

-- A put evaluates all three of its operands and puts the new binding on the front of what is left
-- of the map.
example :
    Eval {} ∅ [lgtm| {hashmap(string, int) with ["a"] = 1}] (.hashmap [(.string "a", .int 1)]) :=
  .EHashmapPut _ _ _ (.EHashmapEmpty _ _) (.EStringLit "a") (.EIntLit 1) rfl

-- All three are evaluated, whatever it took to arrive at them: none of them is in a position to
-- make another unnecessary, the way a comparison's two operands are not.
example :
    Eval {} ∅ [lgtm| {hashmap(string, int) with ["a"] = 1 + 2}]
      (.hashmap [(.string "a", .int 3)]) :=
  .EHashmapPut _ _ _ (.EHashmapEmpty _ _) (.EStringLit "a")
    (.EPlus (n₁ := 1) (n₂ := 2) _ _ (.EIntLit 1) (.EIntLit 2)) rfl

-- Two keys are two bindings, the later one in front.
example :
    Eval {} ∅ [lgtm| {hashmap(string, int) with ["a"] = 1, ["b"] = 2}]
      (.hashmap [(.string "b", .int 2), (.string "a", .int 1)]) :=
  .EHashmapPut _ _ _ (.EHashmapPut _ _ _ (.EHashmapEmpty _ _) (.EStringLit "a") (.EIntLit 1) rfl)
    (.EStringLit "b") (.EIntLit 2) rfl

-- Putting a key the map already binds drops the previous binding rather than shadowing it, which
-- is what `KeyValues.erase?` is in the rule for: a key is bound once, so the value below carries
-- one pair and not two.
example :
    Eval {} ∅ [lgtm| {hashmap(string, int) with ["a"] = 1, ["a"] = 2}]
      (.hashmap [(.string "a", .int 2)]) :=
  .EHashmapPut _ _ _ (.EHashmapPut _ _ _ (.EHashmapEmpty _ _) (.EStringLit "a") (.EIntLit 1) rfl)
    (.EStringLit "a") (.EIntLit 2) rfl

-- A get hands back the option of what the key is bound to.
example : Eval {} ∅ [lgtm| {hashmap(string, int) with ["a"] = 1}["a"]] (.option (some (.int 1))) :=
  .EHashmapGet _ _ (.EHashmapPut _ _ _ (.EHashmapEmpty _ _) (.EStringLit "a") (.EIntLit 1) rfl)
    (.EStringLit "a") rfl

-- A key the map does not bind is the empty option, which is a value like any other rather than
-- anything going wrong: this is the whole of why a get has an option type.
example : Eval {} ∅ [lgtm| {hashmap(string, int) with ["a"] = 1}["b"]] (.option none) :=
  .EHashmapGet _ _ (.EHashmapPut _ _ _ (.EHashmapEmpty _ _) (.EStringLit "a") (.EIntLit 1) rfl)
    (.EStringLit "b") rfl

-- An empty map binds nothing, so every key reads as empty out of one.
example : Eval {} ∅ [lgtm| hashmap(string, int)["a"]] (.option none) :=
  .EHashmapGet _ _ (.EHashmapEmpty _ _) (.EStringLit "a") rfl

-- And a put is what a later get sees, which is the property the two forms exist to have between
-- them.
example :
    Eval {} ∅ [lgtm| {{hashmap(string, int) with ["a"] = 1} with ["a"] = 2}["a"]]
      (.option (some (.int 2))) :=
  .EHashmapGet _ _
    (.EHashmapPut _ _ _ (.EHashmapPut _ _ _ (.EHashmapEmpty _ _) (.EStringLit "a") (.EIntLit 1) rfl)
      (.EStringLit "a") (.EIntLit 2) rfl)
    (.EStringLit "a") rfl

/-- A map binding one `string` to one `int` has the type `hashmap string int`, which is the whole of
what `Value.HasType` asks of one: every key at the key type and every value at the value type. -/
private theorem hasType_mapA {td : TypeDecls} :
    Value.HasType td (.hashmap [(.string "a", .int 1)]) (.hashmap .string .int) :=
  .hashmap
    (fun p hp => by
      obtain rfl : p = (.string "a", .int 1) := by simpa using hp
      exact .string "a")
    (fun p hp => by
      obtain rfl : p = (.string "a", .int 1) := by simpa using hp
      exact .int 1)

/-- An empty one has that type too, and it has every other hashmap type as well — there is nothing
in it for either half to be required of, the way there is nothing in an empty list. -/
private theorem hasType_mapEmpty {td : TypeDecls} {kt vt : Ty} :
    Value.HasType td (.hashmap []) (.hashmap kt vt) :=
  .hashmap (by simp) (by simp)

/-- What `k` is bound to in `m`, and zero when it is bound to nothing. -/
@[lgtm] private def getOr as"get-or"(m : hashmap string int)(k : string) : int :=
  match m[k] with | none => 0 | some(x) => x

#guard (getOr.check {} []).isOk

-- Which case of the match runs is decided by what the lookup produced, so a key the map binds and
-- a key it does not are the two option rules, exactly as for any other option.
example : FuncDecl.Apply getOr {} [] [.hashmap [(.string "a", .int 1)], .string "a"] (.int 1) :=
  .EApply _ (.cons "m" hasType_mapA (.cons "k" (.string "a") .nil))
    (.EOptionMatchSome _ _ _ _ (.EHashmapGet _ _ (.EVarRef "m" rfl) (.EVarRef "k" rfl) rfl)
      (.EVarRef "x" rfl))

example : FuncDecl.Apply getOr {} [] [.hashmap [(.string "a", .int 1)], .string "b"] (.int 0) :=
  .EApply _ (.cons "m" hasType_mapA (.cons "k" (.string "b") .nil))
    (.EOptionMatchNone _ _ _ _ (.EHashmapGet _ _ (.EVarRef "m" rfl) (.EVarRef "k" rfl) rfl)
      (.EIntLit 0))

example : FuncDecl.Apply getOr {} [] [.hashmap [], .string "a"] (.int 0) :=
  .EApply _ (.cons "m" hasType_mapEmpty (.cons "k" (.string "a") .nil))
    (.EOptionMatchNone _ _ _ _ (.EHashmapGet _ _ (.EVarRef "m" rfl) (.EVarRef "k" rfl) rfl)
      (.EIntLit 0))

-- Soundness covers the new forms: the declared result type comes back whatever the map held and
-- whether or not the key was bound, which is what holding both cases of the match to one type was
-- for.
example (kvs : KeyValues) (k : String) (v : Value)
    (h : FuncDecl.Apply getOr {} [] [.hashmap kvs, .string k] v) : v.HasType {} .int :=
  h.hasType Globals.wellTyped_nil
    (by
      simp [getOr, List.lookup]; grind)

-- An argument of the wrong type is stuck at the call, as it is for any other parameter: a map from
-- `string` to `int` is what the declaration asks for, and a list is not one.
example (v : Value) : ¬FuncDecl.Apply getOr {} [] [.list [], .string "a"] v := by
  rintro ⟨-, hargs, -⟩
  cases hargs with
  | cons _ hv _ => cases hv

/-- `m` with `k` bound to `v`, which is the other half: a binding put into a map rather than read
out of one. -/
@[lgtm] private def bind(m : hashmap string int)(k : string)(v : int) : hashmap string int :=
  {m with [k] = v}

#guard (bind.check {} []).isOk

example :
    FuncDecl.Apply bind {} [] [.hashmap [], .string "a", .int 1]
      (.hashmap [(.string "a", .int 1)]) :=
  .EApply _ (.cons "m" hasType_mapEmpty (.cons "k" (.string "a") (.cons "v" (.int 1) .nil)))
    (.EHashmapPut _ _ _ (.EVarRef "m" rfl) (.EVarRef "k" rfl) (.EVarRef "v" rfl) rfl)

-- A put over a key the map already binds replaces it, which is what the result carrying one pair
-- rather than two says.
example :
    FuncDecl.Apply bind {} [] [.hashmap [(.string "a", .int 1)], .string "a", .int 2]
      (.hashmap [(.string "a", .int 2)]) :=
  .EApply _ (.cons "m" hasType_mapA (.cons "k" (.string "a") (.cons "v" (.int 2) .nil)))
    (.EHashmapPut _ _ _ (.EVarRef "m" rfl) (.EVarRef "k" rfl) (.EVarRef "v" rfl) rfl)

/-- What a get means, for every map and key rather than for one: a lookup that produced a value
produced one the map binds.

This is the fact a proof about a hashmap carries on with, the way `Value.equiv_of_beq?` is for a
comparison.  Inverting the rule leaves `KeyValues.lookup?` saying so, and `KeyValues.mem_of_lookup?`
is what turns that into membership. -/
private theorem getOr.mem_of_eval {kvs : KeyValues} {k w : Value}
    (h : Eval {} ⟨[("m", .hashmap kvs), ("k", k)], []⟩ [lgtm| m[k]] (.option (some w))) :
    ∃ k', (k', w) ∈ kvs := by
  cases h with
  | EHashmapGet _ _ hm hk hlookup =>
    cases hm with
    | EVarRef _ hlm =>
      cases hk with
      | EVarRef _ hlk =>
        simp only [Env.lookup, List.lookup] at hlm hlk
        simp_all
        exact KeyValues.mem_of_lookup? hlookup

-- A key that cannot be compared with the keys the map carries leaves both forms stuck, which is the
-- only thing that can go wrong here and is exactly what `Ty.comparable` on the key type rules out.
-- A closure is the thing with no comparison, so a map keyed by one has no lookup at all.
example (body : Expression) (w : Value) :
    ¬Eval {} ⟨[("m", .hashmap [(.closure [] [] [] body, .int 1)])], []⟩
        [lgtm| m[~(Expression.lam [] body)]] (.option w) := by
  intro h
  cases h with
  | EHashmapGet _ _ hm hk hlookup =>
    cases hm with
    | EVarRef _ hlm =>
      cases hk with
      | ELam _ _ =>
        simp [Env.lookup, List.lookup] at hlm
        subst hlm
        simp [KeyValues.lookup?, Value.beq?] at hlookup

/-! ### Converting a map to a list

`toList` is the one hashmap form that compares nothing: the bindings are already the list it hands
back, so the rule has no `KeyValues` premise and nothing about it can go wrong.  What it produces is
one two-element tuple per binding, in the order the map carries them — which is the order they were
put in, since nothing canonicalizes a `Value.hashmap`. -/

-- An empty map converts to the empty list, and the empty list is a list like any other: the tuple
-- type it would have held is the type checker's business, since no value carries one.
example : Eval {} ∅ [lgtm| toList hashmap(string, int)] (.list []) :=
  .EHashmapToList _ (.EHashmapEmpty _ _)

-- One binding is one tuple: the key first and the value it is bound to second.
example :
    Eval {} ∅ [lgtm| toList({hashmap(string, int) with ["a"] = 1})]
      (.list [.tuple [.string "a", .int 1]]) :=
  .EHashmapToList _ (.EHashmapPut _ _ _ (.EHashmapEmpty _ _) (.EStringLit "a") (.EIntLit 1) rfl)

-- Two bindings are two tuples, in the order the map carries them — the later put first, which is
-- where it went when it was put.  This is the order a conversion exposes and nothing else fixes.
example :
    Eval {} ∅ [lgtm| toList({hashmap(string, int) with ["a"] = 1, ["b"] = 2})]
      (.list [.tuple [.string "b", .int 2], .tuple [.string "a", .int 1]]) :=
  .EHashmapToList _
    (.EHashmapPut _ _ _ (.EHashmapPut _ _ _ (.EHashmapEmpty _ _) (.EStringLit "a") (.EIntLit 1) rfl)
      (.EStringLit "b") (.EIntLit 2) rfl)

-- A key put twice is bound once, so it converts to one tuple and not two: what `KeyValues.erase?`
-- did to the map is visible in the list its bindings become.
example :
    Eval {} ∅ [lgtm| toList({hashmap(string, int) with ["a"] = 1, ["a"] = 2})]
      (.list [.tuple [.string "a", .int 2]]) :=
  .EHashmapToList _
    (.EHashmapPut _ _ _ (.EHashmapPut _ _ _ (.EHashmapEmpty _ _) (.EStringLit "a") (.EIntLit 1) rfl)
      (.EStringLit "a") (.EIntLit 2) rfl)

/-- The list one binding converts to has the list-of-tuple type the type checker gives a `toList`:
every element a tuple of as many values as the type has types, each at the type in its position. -/
private theorem hasType_toListA {td : TypeDecls} :
    Value.HasType td (.list [.tuple [.string "a", .int 1]]) (.list (.tuple [.string, .int])) := by
  refine .list fun v hv => ?_
  obtain rfl : v = Value.tuple [.string "a", .int 1] := by simpa using hv
  refine .tuple (by simp) fun p hp => ?_
  rcases (by simpa using hp : p = (Value.string "a", Ty.string) ∨ p = (Value.int 1, Ty.int)) with
    rfl | rfl
  · exact .string "a"
  · exact .int 1

/-- Whether `m` binds anything.

The conversion is what makes this writable: a hashmap has no comparison — its bindings have no
canonical order — while the list they convert to is compared like any other list, against the empty
one. -/
@[lgtm] private def isEmpty as"is-empty"(m : hashmap string int) : bool :=
  toList m == [ : tuple(string, int)]

#guard (isEmpty.check {} []).isOk

-- The comparison is `Value.beq?` on two lists, so the empty map answers `true` and a map binding
-- something answers `false` — on the length alone, with nothing underneath compared.
example : FuncDecl.Apply isEmpty {} [] [.hashmap []] (.bool true) :=
  .EApply _ (.cons "m" hasType_mapEmpty .nil)
    (.EEquals _ _ (.EHashmapToList _ (.EVarRef "m" rfl)) (.ENil _) rfl)

example : FuncDecl.Apply isEmpty {} [] [.hashmap [(.string "a", .int 1)]] (.bool false) :=
  .EApply _ (.cons "m" hasType_mapA .nil)
    (.EEquals _ _ (.EHashmapToList _ (.EVarRef "m" rfl)) (.ENil _) rfl)

-- Soundness covers the form: a `bool` comes back whatever the map held, and the list in the middle
-- has the type `Eval.hasType` reads off the map's.
example (kvs : KeyValues) (v : Value) (h : FuncDecl.Apply isEmpty {} [] [.hashmap kvs] v) :
    v.HasType {} .bool :=
  h.hasType Globals.wellTyped_nil
    (by
      simp [isEmpty, List.lookup]; grind)

-- An argument that is not a map is stuck at the call, as it is for any other parameter.
example (v : Value) : ¬FuncDecl.Apply isEmpty {} [] [.list []] v := by
  rintro ⟨-, hargs, -⟩
  cases hargs with
  | cons _ hv _ => cases hv

/-- What a conversion means, for every map rather than for one: every element of the list it produces
is a binding the map carries, as the tuple of that key and that value.

This is the fact a proof about a converted map carries on with, the way `getOr.mem_of_eval` is for a
lookup.  Inverting the rule leaves `List.map` over the bindings, and that is the whole of it: no
comparison stands between a binding and the tuple it becomes. -/
private theorem isEmpty.mem_of_eval {kvs : KeyValues} {vs : List Value}
    (h : Eval {} ⟨[("m", .hashmap kvs)], []⟩ [lgtm| toList m] (.list vs)) {v : Value}
    (hv : v ∈ vs) : ∃ p ∈ kvs, v = .tuple [p.1, p.2] := by
  cases h with
  | EHashmapToList _ hm =>
    cases hm with
    | EVarRef _ hlm =>
      simp only [Env.lookup, List.lookup] at hlm
      simp_all
      obtain ⟨a, b, hab, rfl⟩ := hv
      exact ⟨a, b, hab, rfl⟩

/-! ### Mapping over a map

`map` is the one hashmap form whose second operand is a function, so it is `EApp` once per binding:
the key and the value it is bound to are the two arguments, `ArgsHaveType` is what holds them to the
closure's parameters, and the body is evaluated in the environment the closure captured rather than
in the one the mapping was written in.

Nothing is compared, as nothing is compared by a conversion, so the keys come back as they were and
in the order they were in.  What can go wrong is what a call can: a second operand that is not a
function at all, and a function the key and the value do not fit. -/

-- An empty map maps to an empty map: there is no binding for the function to be applied to, so both
-- premises over the bindings are vacuous and the function is never entered.
example : Eval {} ∅
    [lgtm| map hashmap(string, int) (fun (k : string) (v : int) => v + 1)] (.hashmap []) :=
  .EHashmapMap (kvs' := []) _ _ (.EHashmapEmpty _ _) (.ELam _ _) rfl (by simp) (by simp)

-- One binding is one call, and the key it was bound under is the key it comes back under: the
-- function is handed both halves of the binding and only the value half is replaced.
example : Eval {} ∅
    [lgtm| map ({ hashmap(string, int) with ["a"] = 1 })
      (fun (k : string) (v : int) => v + 1)]
    (.hashmap [(.string "a", .int 2)]) :=
  .EHashmapMap (kvs' := [(.string "a", .int 2)]) _ _
    (.EHashmapPut _ _ _ (.EHashmapEmpty _ _) (.EStringLit "a") (.EIntLit 1) rfl)
    (.ELam _ _) rfl
    (by rintro p hp
        simp at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact .cons "k" (.string "a") (.cons "v" (.int 1) .nil))
    (by rintro p hp
        simp at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact .EPlus (n₁ := 1) (n₂ := 1) _ _ (.EVarRef "v" rfl) (.EIntLit 1))

-- The function sees the key as well, so a mapping can produce a map whose values are its keys —
-- which is the one way a map's value type changes while its keys stay what they were.
example : Eval {} ∅
    [lgtm| map ({ hashmap(string, int) with ["a"] = 1 })
      (fun (k : string) (v : int) => k)]
    (.hashmap [(.string "a", .string "a")]) :=
  .EHashmapMap (kvs' := [(.string "a", .string "a")]) _ _
    (.EHashmapPut _ _ _ (.EHashmapEmpty _ _) (.EStringLit "a") (.EIntLit 1) rfl)
    (.ELam _ _) rfl
    (by rintro p hp
        simp at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact .cons "k" (.string "a") (.cons "v" (.int 1) .nil))
    (by rintro p hp
        simp at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact .EVarRef "k" rfl)

-- A second operand that is not a function leaves this stuck, which is one of the two things that
-- can go wrong here and is exactly what typing rules out.
example (v : Value) : ¬Eval {} ∅ [lgtm| map hashmap(string, int)1] v := by
  intro h
  cases h with
  | EHashmapMap _ _ _ hf _ _ _ => cases hf

/-- Every value of `m` with one added to it, the keys left as they were: the shortest declaration
the form is in, and the one place a map is read by something other than a key.

It is also where a mapping over a *name* is written: the parameter's declared type is what the
keyword is read by, where a fragment has none to read and would take this for a list's mapping. -/
@[lgtm] private def bump (m : hashmap string int) : hashmap string int :=
  map m (fun (k : string) (v : int) => v + 1)

#guard (bump.check {} []).isOk

-- The closure the function evaluates to captures the call's environment, so the body runs over the
-- parameters of the `fun` in front of `m` — the same way a call into a closure runs it.
example :
    FuncDecl.Apply bump {} [] [.hashmap [(.string "a", .int 1)]]
      (.hashmap [(.string "a", .int 2)]) :=
  .EApply _ (.cons "m" hasType_mapA .nil)
    (.EHashmapMap (kvs' := [(.string "a", .int 2)]) _ _ (.EVarRef "m" rfl) (.ELam _ _) rfl
      (by
        rintro p hp
        simp at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact .cons "k" (.string "a") (.cons "v" (.int 1) .nil))
      (by
        rintro p hp
        simp at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact .EPlus (n₁ := 1) (n₂ := 1) _ _ (.EVarRef "v" rfl) (.EIntLit 1)))

-- An empty map is the one argument that needs neither premise, since there is no binding to apply
-- the function to.
example : FuncDecl.Apply bump {} [] [.hashmap []] (.hashmap []) :=
  .EApply _ (.cons "m" hasType_mapEmpty .nil)
    (.EHashmapMap (kvs' := []) _ _ (.EVarRef "m" rfl) (.ELam _ _) rfl (by simp) (by simp))

-- Soundness covers the form: the declared map type comes back whatever the map held, with the key
-- half carried through from the argument and the value half read off the function's body.
example (kvs : KeyValues) (v : Value) (h : FuncDecl.Apply bump {} [] [.hashmap kvs] v) :
    v.HasType {} (.hashmap .string .int) :=
  h.hasType Globals.wellTyped_nil
    (by
      -- The two types the function's parameters are compared against are the map's, and `string` is
      -- the key type the comparability condition is about.
      simp [bump, List.lookup]
      exact ⟨.string, .int, ⟨rfl, rfl⟩, .int, ⟨⟨rfl, rfl⟩, rfl⟩, by decide, rfl, rfl⟩)

-- A function the key and the value do not fit is the other thing that can go wrong: the arguments
-- are the binding, so `ArgsHaveType` turns down a function expecting an `int` key exactly as a call
-- with the wrong argument types is turned down.  The expression is written out rather than as a
-- fragment, since a `map` over a name with no type to read is a list's mapping.
example (v : Value) :
    ¬ Eval {} ⟨[("m", .hashmap [(.string "a", .int 1)])], []⟩
      (Expression.hashmapMap (.varRef "m") (.lam [("k", .int), ("v", .int)] (.varRef "v"))) v := by
  intro h
  cases h with
  | @EHashmapMap _ _ _ _ _ _ kvs' _ _ hm hf hkeys hat _ =>
      cases hm with
      | EVarRef _ hlm =>
          cases hf with
          | ELam _ _ =>
              simp [Env.lookup, List.lookup] at hlm
              subst hlm
              -- The keys of the map it built are the keys it was given, so it has one binding, and
              -- that binding's key is the `string` the function has no parameter for.
              obtain ⟨q', rfl⟩ : ∃ q', kvs' = [q'] := by
                cases kvs' with
                | nil => simp at hkeys
                | cons q' rest =>
                    cases rest with
                    | nil => exact ⟨q', rfl⟩
                    | cons _ _ => simp at hkeys
              cases hat ((.string "a", .int 1), q') (by simp) with
              | cons _ hv _ => cases hv

/-- What a mapping means, for every map rather than for one: the keys of the map it produces are the
keys of the map it was given.

This is the fact a proof about a mapped map carries on with, the way `isEmpty.mem_of_eval` is for a
converted one.  Inverting the rule leaves exactly that equality — the values are what the calls
produced, and the keys are what no call was made about.

Stated over `bump.body` rather than a fragment, since that is where a mapping over a name is read as
a hashmap's: the declaration's parameter is what gives `m` the type the keyword is read by. -/
private theorem bump.keys_of_eval {kvs kvs' : KeyValues}
    (h : Eval {} ⟨[("m", .hashmap kvs)], []⟩ bump.body (.hashmap kvs')) :
    kvs.map Prod.fst = kvs'.map Prod.fst := by
  cases h with
  | EHashmapMap _ _ hm _ hkeys _ _ =>
      cases hm with
      | EVarRef _ hlm =>
          simp [Env.lookup, List.lookup] at hlm
          subst hlm
          exact hkeys

/-! ## Tuples

The two forms a tuple is built and taken apart by.  Building one is `EIndNew` without a constructor
to name — one evaluation per element, in the order they were written — and reading one is
`EStructGet` by position instead of by name, so the two ways either can go wrong are the two ways
those can: nothing at all for the first, and an index the value has nothing at for the second. -/

-- Building one evaluates each element and keeps the values in order.  The empty tuple evaluates
-- nothing, which is what makes it the one value of `tuple()`.
example : Eval {} ∅ [lgtm| tuple()] (.tuple []) :=
  .ETupleNew (vs := []) _ rfl (by simp)

example : Eval {} ∅ [lgtm| tuple(1, "a")] (.tuple [.int 1, .string "a"]) :=
  .ETupleNew (vs := [.int 1, .string "a"]) _ rfl
    (by
      rintro p hp
      simp at hp
      rcases hp with rfl | rfl
      · exact .EIntLit 1
      · exact .EStringLit "a")

-- The order is the order the elements were written, which is the whole of what a tuple records: the
-- same two values the other way round are a different value at a different type.
example : Eval {} ∅ [lgtm| tuple("a", 1)] (.tuple [.string "a", .int 1]) :=
  .ETupleNew (vs := [.string "a", .int 1]) _ rfl
    (by
      rintro p hp
      simp at hp
      rcases hp with rfl | rfl
      · exact .EStringLit "a"
      · exact .EIntLit 1)

-- Reading one hands back the value at that position, whatever its type: a tuple is heterogeneous,
-- so the two reads of one pair produce values of two types.
example : Eval {} ⟨[("t", .tuple [.string "a", .int 1])], []⟩ [lgtm| t.0] (.string "a") :=
  .ETupleGet _ _ (.EVarRef "t" rfl) rfl

example : Eval {} ⟨[("t", .tuple [.string "a", .int 1])], []⟩ [lgtm| t.1] (.int 1) :=
  .ETupleGet _ _ (.EVarRef "t" rfl) rfl

-- The two forms compose, so building and reading back is the identity on each position.
example : Eval {} ∅ [lgtm| tuple(1, "a").1] (.string "a") :=
  .ETupleGet _ _
    (.ETupleNew (vs := [.int 1, .string "a"]) _ rfl
      (by
        rintro p hp
        simp at hp
        rcases hp with rfl | rfl
        · exact .EIntLit 1
        · exact .EStringLit "a"))
    rfl

-- An index the value has nothing at leaves a read stuck, which is the only thing that can go wrong
-- here and is exactly what typing rules out — the index is in the expression, so `Expression.infer`
-- has already read the type at it.
example (v : Value) : ¬Eval {} ⟨[("t", .tuple [.string "a", .int 1])], []⟩ [lgtm| t.2] v := by
  intro h
  cases h with
  | ETupleGet _ _ ht hget =>
    cases ht with
    | EVarRef _ hlt =>
      simp [Env.lookup, List.lookup] at hlt
      subst hlt
      simp at hget

-- And so does a read of something that is not a tuple at all, a list of the same values included:
-- the value says which of the two it is, and nothing converts between them.
example (v : Value) : ¬Eval {} ⟨[("t", .list [.string "a"])], []⟩ [lgtm| t.0] v := by
  intro h
  cases h with
  | ETupleGet _ _ ht _ =>
    cases ht with
    | EVarRef _ hlt => simp [Env.lookup, List.lookup] at hlt

/-- The first half of a pair of a `string` and an `int`, which is the shortest declaration the two
forms are both in: a parameter of tuple type read at one position. -/
@[lgtm] private def fst(t : tuple(string, int)) : string := t.0

/-- And the pair itself, which is the other half: a declaration whose result type is a tuple. -/
@[lgtm] private def pair(s : string)(n : int) : tuple(string, int) := tuple(s, n)

-- A tuple names nothing, so both check against no `TypeDecls` at all.
#guard (fst.check {} []).isOk

#guard (pair.check {} []).isOk

/-- A pair of a `string` and an `int` has the tuple type of those two, which is as much as a tuple
value's type ever needs: there is no declaration to resolve, so the length and the two positions are
the whole of it. -/
private theorem hasType_pairA {td : TypeDecls} :
    Value.HasType td (.tuple [.string "a", .int 1]) (.tuple [.string, .int]) :=
  .tuple (by simp)
    (by
      rintro p hp
      simp at hp
      rcases hp with rfl | rfl
      · exact .string "a"
      · exact .int 1)

example : FuncDecl.Apply fst {} [] [.tuple [.string "a", .int 1]] (.string "a") :=
  .EApply _ (.cons "t" hasType_pairA .nil) (.ETupleGet _ _ (.EVarRef "t" rfl) rfl)

example : FuncDecl.Apply pair {} [] [.string "a", .int 1] (.tuple [.string "a", .int 1]) :=
  .EApply _ (.cons "s" (.string "a") (.cons "n" (.int 1) .nil))
    (.ETupleNew (vs := [.string "a", .int 1]) _ rfl
      (by
        rintro p hp
        simp at hp
        rcases hp with rfl | rfl
        · exact .EVarRef "s" rfl
        · exact .EVarRef "n" rfl))

-- Soundness covers both forms: a `string` comes back from the read whatever the pair held, and the
-- value the build produced has the declared tuple type.
example (v w : Value) (h : FuncDecl.Apply fst {} [] [.tuple [v, w]] (.string "a")) :
    Value.HasType {} (.string "a") .string :=
  h.hasType Globals.wellTyped_nil (by simp [fst, List.lookup])

example (s : String) (n : Int) (v : Value) (h : FuncDecl.Apply pair {} [] [.string s, .int n] v) :
    v.HasType {} (.tuple [.string, .int]) :=
  h.hasType Globals.wellTyped_nil (by simp [pair, List.lookup])

-- An argument that is not a tuple is stuck at the call, as it is for any other parameter: a list of
-- the same two values will not do.
example (v : Value) : ¬FuncDecl.Apply fst {} [] [.list [.string "a", .int 1]] v := by
  rintro ⟨-, hargs, -⟩
  cases hargs with
  | cons _ hv _ => cases hv

-- Nor will a pair of the two types the other way round, which is the one thing a tuple's length and
-- order being part of its type comes to.
example (v : Value) : ¬FuncDecl.Apply fst {} [] [.tuple [.int 1, .string "a"]] v := by
  rintro ⟨-, hargs, -⟩
  cases hargs with
  | cons _ hv _ =>
    obtain ⟨ts, hlen, htys, heq⟩ := Value.hasType_tuple_iff.mp hv
    obtain rfl : ts = [.string, .int] := by simpa using heq.symm
    cases htys (.int 1, .string) (by simp)

/-- What a read means, for every pair rather than for one: the value it hands back is the value the
tuple carried at that position.

This is the fact a proof about a tuple carries on with, the way `isEmpty.mem_of_eval` is for a
converted map.  Inverting the rule leaves `getElem?` on the values and that is the whole of it: no
comparison and no declaration stands between a position and what is at it. -/
private theorem fst.eq_of_eval {vs : List Value} {v : Value}
    (h : Eval {} ⟨[("t", .tuple vs)], []⟩ [lgtm| t.0] v) : vs[0]? = some v := by
  cases h with
  | ETupleGet _ _ ht hget =>
    cases ht with
    | EVarRef _ hlt =>
      simp [Env.lookup, List.lookup] at hlt
      subst hlt
      exact hget

/-! ## An unreachable branch

The one form `Eval` has no rule for, worked through the way every other stuck case is — except that
this one is stuck for a *well-typed* expression, which is what makes reaching it something a proof
rules out rather than something the type checker already did. -/

/-- One less than a positive `n`.  The `else` is the branch the guard rules out, so it is written as
the unreachable it is: annotated `int` because the branch beside it is, and evaluated by nothing. -/
@[lgtm] private def pred(n : int) : int :=
  if 0 < n then (n - 1) else (unreachable"n is positive" : int)

#guard (pred.check {} []).isOk

-- Nothing evaluates it, whatever it is annotated with and whatever is in the environment.
example (env : Env) (v : Value) : ¬Eval {} env [lgtm| unreachable"why" : int] v :=
  Eval.not_unreachable

example (env : Env) (t : Ty) (why : String) (v : Value) : ¬Eval {} env (.unreachable t why) v :=
  Eval.not_unreachable

-- A call down the branch the guard allows returns what it says, exactly as any other `ite` does.
example : FuncDecl.Apply pred {} [] [.int 3] (.int 2) :=
  .EApply _ (.cons "n" (.int 3) .nil)
    (.EIteTrue _ _ _ (.ELt _ _ (.EIntLit 0) (.EVarRef "n" rfl) rfl)
      (.EMinus (n₁ := 3) (n₂ := 1) _ _ (.EVarRef "n" rfl) (.EIntLit 1)))

-- A call on a non-positive argument returns nothing at all: the guard sends it to the `unreachable`,
-- and that is where it stops.  This is the fact a use of the form is proved safe by — the call is
-- well typed, so being stuck here is not something typing had already ruled out.
example (v : Value) : ¬FuncDecl.Apply pred {} [] [.int 0] v := by
  rintro ⟨-, -, hbody⟩
  cases hbody with
  | EIteTrue _ _ _ hc _ =>
    -- The guard came out `true`, which is what `0 < 0` is not.
    cases hc with
    | ELt _ _ h₀ hn hlt =>
      cases h₀
      cases hn with
      | EVarRef _
        hlookup =>
        simp [pred, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup] at hlookup
        subst hlookup
        simp at hlt
  | EIteFalse _ _ _ _ hels => exact Eval.not_unreachable hels

-- Reaching it is the only way a well-typed call of `pred` gets stuck, which is what carries over to
-- a proof *about* the branch: anything the call returns came from the branch the guard allows, so
-- `0 < n` holds of whatever was passed.
example (n : Int) (v : Value) (h : FuncDecl.Apply pred {} [] [.int n] v) : 0 < n := by
  obtain ⟨-, -, hbody⟩ := h
  cases hbody with
  | EIteTrue _ _ _ hc _ =>
    cases hc with
    | ELt _ _ h₀ hn hlt =>
      cases h₀
      cases hn with
      | EVarRef _
        hlookup =>
        simp [pred, FuncDecl.callEnv, Env.extend, Globals.env, Env.lookup] at hlookup
        subst hlookup
        simpa using hlt
  | EIteFalse _ _ _ _ hels => exact absurd hels Eval.not_unreachable

-- Soundness is unaffected: a value that comes back is still of the declared type, and the
-- annotation on a branch nothing reached never had to agree with one.
example (n : Int) (v : Value) (h : FuncDecl.Apply pred {} [] [.int n] v) : v.HasType {} .int :=
  h.hasType Globals.wellTyped_nil (by simp [pred, List.lookup])
