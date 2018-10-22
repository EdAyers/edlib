namespace set

universes u v

variables {α : Type u} {ι : Type v}

variables {A B C D X Y : set α}
variables {a b c : α}

theorem ext (h : ∀ a, a ∈ A ↔ a ∈ B) : A = B :=
funext (λ a, propext (h a))

lemma pair₁ : a ∈ ({a,b} : set α) := begin apply or.inr, apply or.inl, refl end
lemma pair₂ : b ∈ ({a,b} : set α) := begin apply or.inl, refl end

@[refl] theorem subset.refl : A ⊆ A := λ _ m, m
@[trans] theorem subset.trans (s₁ : A ⊆ B) (s₂ : B ⊆ C) : A ⊆ C := λ _ ma, s₂ $ s₁ ma
theorem subset.antisymm (l : A ⊆ B) (r : B ⊆ A) : A = B := ext (λ _, ⟨λ m, l m, λ m, r m⟩)
theorem union.empty : ⋃₀(∅ : set (set α)) = ∅ := ext $ λ a, ⟨λ ⟨_,o,_⟩, false.rec_on _ o, λ o, false.rec_on _ o⟩
theorem inter.π₁ : A ∩ B ⊆ A := λ x a, a.1
theorem inter.π₂ : A ∩ B ⊆ B := λ x a, a.2
theorem union.ι {ℱ : set $ set α} {U : set α} : U ∈ ℱ →  U ⊆ ⋃₀ ℱ := λ Uℱ a aU, ⟨U, Uℱ, aU⟩
/--Universality of intersection-/
theorem subset.inter : X ⊆ A → X ⊆ B → X ⊆ A ∩ B
:= λ a b x h, ⟨a h, b h⟩
theorem subset.inter_subset_inter : A ⊆ B → C ⊆ D → A ∩ C ⊆ B ∩ D
:= λ ab cd _ ⟨hA,hC⟩, ⟨ab hA, cd hC⟩
theorem subset.empty : ∅ ⊆ A := λ o oh, false.rec_on _ oh
theorem subset.univ : A ⊆ univ := λ _ _, ⟨⟩
theorem inter.empty : ∅ ∩ A = ∅ := ext (λ x, ⟨λ ⟨a,_⟩, a, λ x, false.rec_on _ x⟩)
theorem inter.univ : univ ∩ A = A := ext (λ x, ⟨λ ⟨_,a⟩, a, λ mA, ⟨⟨⟩,mA⟩⟩) 
theorem inter_comm (X Y : set α) : X ∩ Y = Y ∩ X := ext $ λ a, and.comm
theorem inter_assoc (A B C : set α): (A ∩ B) ∩ C = A ∩ (B ∩ C) := ext $ λ a, and.assoc
instance inter_is_assoc : is_associative (set α) (∩) := ⟨inter_assoc⟩
instance inter_is_comm : is_commutative (set α) (∩) := ⟨inter_comm⟩

def sInter (G : set (set α)) : set α := {x | ∀ A ∈ G, x ∈ A}
prefix `⋂₀`:110 := sInter
/- indexed intersection -/
def Inter  (s : ι → set α) : set α :=  {x : α | ∀i : ι, x ∈ s i}

/-- Indexed union of a family of sets -/
@[reducible] def Union {β} (s : ι → set β) : set β := {a : β | ∃ i : ι, a ∈ s i}


notation `⋃` binders `, ` r:(scoped f, Union f) := r
notation `⋂` binders `, ` r:(scoped f, Inter f) := r
def triv_insert {α : Type*} {a : α} : a ∈ ({a} : set α) := or.inl rfl

def sInter.univ_singleton : ⋂₀ {(univ : set α)} = (univ : set α) := 
ext $ λ a, ⟨λ h, h univ $ or.inl rfl, λ h A H, or.rec_on H (λ p, eq.symm p ▸ h) (λ o, false.rec_on _ o)⟩

def Inter_compl {s : ι → set α} : (⋂ i, s i) = - (⋃ i, - (s i))
:= set.ext $ λ a, ⟨λ h₁ ⟨i,h₂⟩, h₂ (h₁ i),λ h₁ i, classical.by_contradiction (λ h₂, h₁ ⟨i,h₂⟩)⟩

def function (dom : set α) (cod : set α) : Type u := {x // x ∈ dom} → {y // y ∈ cod}


end set