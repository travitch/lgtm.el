module

/-- An n-ary tree. -/
public structure Tree (α : Type) where
  /-- The value at this tree node. -/
  value : α
  /-- The children of this tree node. -/
  children : List α

/-- Add CHILD to this TREE node.

    The child is prepended to the list of children. -/
public def Tree.addChild (tree : Tree α) (child : α) : Tree α :=
  ⟨tree.value, child :: tree.children⟩
