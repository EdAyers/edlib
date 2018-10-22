import order.filter analysis.metric_space
open filter set
/- Non standard analysis -/

/-- The filter of sets of natural numbers with finite complement. -/
def frechet : filter ℕ :=
{ sets := {X : set ℕ | set.finite (- X)}
, univ_sets := begin simp end
, sets_of_superset := λ A B h₁ h₂, finite_subset h₁ $ λ x h₃ h₄, h₃ $ h₂ h₄
, inter_sets := begin intros, simp, rw [compl_inter], apply finite_union, repeat {assumption} end
}
/- [TODO] show it's an ultrafilter. -/

/-- A sequence of reals. Think of them as 'schedules' -/
def rs := ℕ → ℝ

instance feq (ℱ : filter ℕ := frechet) : setoid rs :=
{ r := λ σ ρ, {n : ℕ| σ n = ρ n} ∈ ℱ.sets
, iseqv := 
    ⟨ λ σ, begin simp, apply ℱ.univ_sets end
    , λ σ₁ σ₂ p , have h : {n : ℕ | σ₂ n = σ₁ n} = {n : ℕ | σ₁ n = σ₂ n}, from set.ext $ λ x, ⟨eq.symm,eq.symm⟩ , by simp [h]; apply p
    , λ σ₁ σ₂ σ₃ p₁₂ p₂₃, ℱ.sets_of_superset (ℱ.inter_sets p₁₂ p₂₃) (λ n ⟨a,b⟩, eq.trans a b)
    ⟩
}

def hyperreal := @quotient rs feq

def of_real : real → hyperreal := λ x, @quotient.mk _ feq (λ n, x)

/-- An infinitesimal? -/
noncomputable def ε : hyperreal := @quotient.mk _ feq $ λ n, 1 / (n + 1)

/- [TODO] show it's a field. -/