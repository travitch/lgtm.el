module

public structure Tree (α : Type) where
  value : α
  children : List α

public def Tree.addChild (tree : Tree α) (child : α) : Tree α :=
  ⟨tree.value, child :: tree.children⟩
