
namespace set

universes u v

variables {α : Type u} {ι : Type v}

variables {A B C D X Y : set α}

theorem ext (h : ∀ a, a ∈ A ↔ a ∈ B) : A = B :=
funext (λ a, propext (h a))

@[refl] theorem subset.refl : A ⊆ A := λ _ m, m
@[trans] theorem subset.trans (s₁ : A ⊆ B) (s₂ : B ⊆ C) : A ⊆ C := λ _ ma, s₂ $ s₁ ma
theorem subset.antisymm (l : A ⊆ B) (r : B ⊆ A) : A = B := ext (λ _, ⟨λ m, l m, λ m, r m⟩)

theorem subset.π₁ : A ∩ B ⊆ A := λ x a, a.1
theorem subset.π₂ : A ∩ B ⊆ B := λ x a, a.2
/--Universality of intersection-/
theorem subset.inter : X ⊆ A → X ⊆ B → X ⊆ A ∩ B
:= λ a b x h, ⟨a h, b h⟩
theorem subset.inter_subset_inter : A ⊆ B → C ⊆ D → A ∩ C ⊆ B ∩ D
:= λ ab cd _ ⟨hA,hC⟩, ⟨ab hA, cd hC⟩
theorem subset.empty : ∅ ⊆ A := λ o oh, false.rec_on _ oh
theorem subset.univ : A ⊆ univ := λ _ _, ⟨⟩

theorem inter_comm (X Y : set α) : X ∩ Y = Y ∩ X := ext $ λ a, and.comm
theorem inter_assoc (A B C : set α): (A ∩ B) ∩ C = A ∩ (B ∩ C) := ext $ λ a, and.assoc
instance inter_is_assoc : is_associative (set α) (∩) := ⟨inter_assoc⟩
instance inter_is_comm : is_commutative (set α) (∩) := ⟨inter_comm⟩

def sInter (G : set (set α)) : set α := {x | ∀ A ∈ G, x ∈ A}
prefix `⋂₀`:110 := sInter
/- indexed intersection -/
def iInter  (s : ι → set α) : set α :=  {x : α | ∀i : ι, x ∈ s i}

notation `⋂` binders `, ` r:(scoped f, iInter f) := r
def triv_insert {α : Type*} {a : α} : a ∈ ({a} : set α) := or.inl rfl

def sInter.univ_singleton : ⋂₀ {(univ : set α)} = (univ : set α) := 
ext $ λ a, ⟨λ h, h univ $ or.inl rfl, λ h A H, or.rec_on H (λ p, eq.symm p ▸ h) (λ o, false.rec_on _ o)⟩
 

end set