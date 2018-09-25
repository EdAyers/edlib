universes u
variables {α β : Type u}

/-- A Galois connection is a pair of functions `l` and `u` satisfying
  `l a ≤ b ↔ a ≤ u b`. They are closely connected to adjoint functors
  in category theory. -/
def galois_connection [preorder α] [preorder β] 
  (l : α → β) (u : β → α) := ∀a b, l a ≤ b ↔ a ≤ u b

