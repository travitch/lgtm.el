module

public structure Tree (α : Type) where
  value : α
  children : List α

public def Tree.addChild (t : Tree α) (child : α) : Tree α :=
  ⟨t.value, child :: t.children⟩
