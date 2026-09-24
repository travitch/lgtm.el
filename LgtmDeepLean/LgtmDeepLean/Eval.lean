module

public import LgtmDeepLean.IR
public import LgtmDeepLean.TypeCheck

public inductive Value where
| int : Int → Value
| list : List Value → Value

/-- The `Ty` a value's representation agrees with.

A list value is homogeneous: every element has the list's single element type. -/
public inductive Value.HasType : Value → Ty → Prop where
| int (i : Int) : HasType (.int i) .int
| list {vs : List Value} {t : Ty} : (∀ v ∈ vs, HasType v t) → HasType (.list vs) (.list t)

public abbrev Env := List (String × Value)

public inductive Eval (env : Env) : Expression → Value → Prop where
| EIntLit (i : Int) : Eval env (.intLit i) (.int i)
| EPlus (e₁ : Expression) (e₂ : Expression) : Eval env e₁ (.int n₁) → Eval env e₂ (.int n₂) → Eval env (.plus e₁ e₂) (.int (n₁ + n₂))
| EMinus (e₁ : Expression) (e₂ : Expression) : Eval env e₁ (.int n₁) → Eval env e₂ (.int n₂) → Eval env (.minus e₁ e₂) (.int (n₁ - n₂))
| ENil (ty : Ty) : Eval env (.lnil ty) (.list [])
| ECons (e₁ : Expression) (e₂ : Expression) : Eval env e₁ v → Eval env e₂ (.list vs) → Eval env (.lcons e₁ e₂) (.list (v :: vs))

/-- Evaluating a well-typed expression produces a value of its inferred type.

`ECons` needs no premise relating the new element to the rest of the list: `Expression.infer`
already requires the tail to be a list of the element type read off the head, so the values
`ECons` builds are homogeneous whenever the expression it evaluates is well typed. -/
public theorem Eval.hasType {env : Env} {ctx : Context} {e : Expression} {v : Value} {t : Ty}
    (h : Eval env e v) (ht : e.infer ctx = some t) : v.HasType t := by
  induction h generalizing t with
  | ECons e₁ e₂ h₁ h₂ ih₁ ih₂ =>
      obtain ⟨t', ht₁, ht₂, rfl⟩ := Expression.infer_lcons_eq_some.mp ht
      have hv := ih₁ ht₁
      cases ih₂ ht₂ with
      | list hall => exact .list (by grind)
  | _ => grind [Value.HasType]
