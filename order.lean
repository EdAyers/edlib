def order_dual (α : Type*) := α

namespace order_dual
instance has_le (α : Type*) [has_le α] : has_le (order_dual α) := ⟨λx y:α, y ≤ x⟩
instance has_lt (α : Type*) [has_lt α] : has_lt (order_dual α) := ⟨λx y:α, y < x⟩

instance has_preorder (α : Type*) [preorder α] : preorder (order_dual α) :=
{ le_refl  := le_refl,
  le_trans := assume a b c hab hbc, le_trans hbc hab,
  .. order_dual.has_le α 
}
instance has_partial_order (α : Type*) [po : partial_order α] : partial_order (order_dual α) :=
{ le_antisymm := begin intros, apply @le_antisymm _ po, assumption, assumption end
, ..(order_dual.has_preorder α)
}
instance has_linear_order (α : Type*) [po : linear_order α] : linear_order (order_dual α) :=
{ le_total := λ a b, or.swap $ le_total a b
, ..(order_dual.has_partial_order α)
}
instance has_decidable_le (α : Type*) [hle : has_le α] [d : decidable_rel hle.le] 
    : decidable_rel (order_dual.has_le α).le := λ x y, d y x
instance has_decidable_lt (α : Type*) [hlt : has_lt α] [d : decidable_rel hlt.lt] 
    : decidable_rel (order_dual.has_lt α).lt := λ x y, d y x
lemma transitive_lt (α : Type*) [hlt : has_lt α] [tr : transitive hlt.lt] 
    : transitive (@order_dual.has_lt α hlt).lt := λ x y z p q, tr q p

instance has_decidable_linear_order (α : Type*) [dlo : decidable_linear_order α]
    : decidable_linear_order (order_dual α) :=
{  decidable_eq := λ a b, @decidable_linear_order.decidable_eq α dlo a b
, decidable_le := λ a b, @decidable_linear_order.decidable_le α dlo b a
, ..(order_dual.has_linear_order α)
}
end order_dual