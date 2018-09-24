-- The rational numbers.
-- I wonder what the minimal amount of code it takes to define the Real numbers is.

universe u


namespace field 

-- IDEA: the free field over an integral_domain.

structure q (α : Type u) [integral_domain α]:= (n : α) (d : {a :α// a ≠ 0})
instance (α : Type u) [integral_domain α] : setoid (q α) :=
{ r := (λ a b, a.1 * b.2 = b.1 * a.2)
, iseqv := 
  ⟨ λ a, rfl
  , λ a b p, eq.symm p
  , λ ⟨n₁,d₁,_⟩ ⟨n₂,d₂,h⟩ ⟨n₃,d₃,_⟩ (p : n₁ * d₂ = n₂ * d₁) (q : n₂ * d₃ = n₃ * d₂),
    suffices d₂ * (n₁ * d₃) = d₂ * (n₃ * d₁), from eq_of_mul_eq_mul_left h this,
    calc
      d₂ * (n₁ * d₃) = (n₁ * d₂) * d₃ : by ac_refl
                ...  = (n₂ * d₁) * d₃ : by rw p
                ...  = (n₂ * d₃) * d₁ : by ac_refl
                ...  = (n₃ * d₂) * d₁ : by rw q
                ...  = d₂ * (n₃ * d₁) : by ac_refl
  ⟩
}

#check @quotient

def free (α : Type u) [integral_domain α] : Type* := @quotient (q α) (by apply_instance)
variables {α : Type u} [integral_domain α]

def free.add : free α → free α → free α 
:= λ x y, quotient.lift_on₂ x y 
  (λ x y, ⟦(⟨x.1 * y.2 + y.1 * x.2, x.2 * y.2, mul_ne_zero x.2.2 y.2.2⟩ : q α)⟧) 
  (λ a1 a2 b1 b2,
      assume p : a1.1 * b1.2 = b1.1 * a1.2,
      assume q : a2.1 * b2.2 = b2.1 * a2.2,
      suffices (a1.1 * a2.2 + a2.1 * a1.2) * (b1.2 * b2.2) = (b1.1 * b2.2 + b2.1 * b1.2) * (a1.2 * a2.2), 
        from quotient.sound this,
      calc (a1.1 * a2.2 + a2.1 * a1.2) * (b1.2 * b2.2) = ((a1.1 * a2.2) * (b1.2 * b2.2) + (a2.1 * a1.2) * (b1.2 * b2.2)) : by apply right_distrib _ _ (b1.2.1 * b2.2.1)
                                                  ...  = ((a1.1 * b1.2) * (a2.2 * b2.2) + (b1.2 * a1.2) * (a2.1 * b2.2)) : by ac_refl
                                                  ...  = ((b1.1 * a1.2) * (a2.2 * b2.2) + (b1.2 * a1.2) * (b2.1 * a2.2)) : by rw p; rw q
                                                  ...  = (((b1.1 * b2.2)* (a1.2 * a2.2)) + ((b2.1 * b1.2) * (a1.2 * a2.2)))   : by ac_refl
                                                  ...  = (b1.1 * b2.2 + b2.1 * b1.2) * (a1.2 * a2.2)                     : by apply eq.symm; apply right_distrib

  )



-- -- def add : free α → free α → free α
-- -- |⟦⟨a,b⟩⟧ ⟦⟨x,y⟩⟧ := ⟦⟨a * y + x * b, b * y⟩⟧

-- -- [TODO] : prove it's a division ring
-- instance : division_ring (free α) := sorry
-- instance [comm_ring α] : field (free α) := sorry
-- -- instance [comm_ring α] [ordered_ring α] : ordered_field (free α) := sorry
-- -- [TODO] : the idea is to prove a chain of adjunctions, then show that division ring -> field is reflective. 
-- -- lots of things lift in ways that I find interesting. Eg ring -> field lifts orderings.
-- -- [TODO] : write a functor (ordered field -> complete field)

-- -- I wonder if you do universal algebra first, you can get all of this structure for free?

end field