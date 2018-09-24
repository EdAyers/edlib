-- The rational numbers.
-- I wonder what the minimal amount of code it takes to define the Real numbers is.

namespace division_ring 

universe u
-- IDEA: the free field over a ring.
def free (α : Type u) [ring α] : Type u := @quot (α × α) (λ ⟨a,b⟩ ⟨x,y⟩, a * y = b * x)
variables {α : Type u} [ring α]

-- def add : free α → free α → free α
-- |⟦⟨a,b⟩⟧ ⟦⟨x,y⟩⟧ := ⟦⟨a * y + x * b, b * y⟩⟧

-- [TODO] : prove it's a division ring
instance : division_ring (free α) := sorry
instance [comm_ring α] : field (free α) := sorry
-- instance [comm_ring α] [ordered_ring α] : ordered_field (free α) := sorry
-- [TODO] : the idea is to prove a chain of adjunctions, then show that division ring -> field is reflective. 
-- lots of things lift in ways that I find interesting. Eg ring -> field lifts orderings.
-- [TODO] : write a functor (ordered field -> complete field)

-- I wonder if you do universal algebra first, you can get all of this structure for free?

end division_ring