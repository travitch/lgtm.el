module

public structure Tree (α : Type) where
  value : α
  children : List (Tree α)


public def Tree.addChild (t : Tree α) (child : Tree α) : Tree α :=
  ⟨t.value, child :: t.children⟩
