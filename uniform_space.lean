import .topology

open topology filter
universe u
variables {α : Type u}
def prod.swap {β:Type*} : α × β → β × α
|⟨a,b⟩ := ⟨b,a⟩
def rel.comp {α β γ : Type*} : set (α × β) → set (β × γ) → set (α × γ) := λ R S, {p|∃ b : β, prod.mk p.1 b ∈ R ∧ prod.mk b p.2 ∈ S}
instance : has_inv (set (α × α)) := ⟨λ R, {p| prod.mk p.2 p.1 ∈ R}⟩

class uniformity (X : Type u) :=
(Φ : filter (X × X))
(refl : ∀ (R ∈ Φ) (x : X), prod.mk x x ∈ R)
(symm : ∀ (R ∈ Φ), R⁻¹ ∈ Φ)
(sqrt : ∀ (R ∈ Φ), ∃ V ∈ Φ, rel.comp V V = R )

namespace uniformity 
variables {X : Type u } [uniformity X]
open uniformity
def topology_of_uniformity : topology X :=
{ 𝒪 := {U|∀ x ∈ U, {p:X×X|p.1 = x → p.2 ∈ U} ∈ Φ(X)}
, top := λ (x : X) _, begin apply filter.sets_of_superset, apply filter.univ_sets, intros x _ _, trivial end
, i := λ U V h₁ h₂ x h₃, filter.sets_of_superset _ (filter.inter_sets _ (h₁ _ h₃.1) (h₂ _ h₃.2)) (λ p ⟨i,j⟩ h₄, ⟨i h₄, j h₄⟩)
, U := λ ℱ ss x ⟨U, Uℱ, xU⟩, begin apply filter.sets_of_superset, apply ss, apply Uℱ, apply xU, intros p h₁ h₂, apply set.union.ι Uℱ, apply h₁ h₂   end
}



end uniformity

