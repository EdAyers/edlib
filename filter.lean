
import .set .lattice
open set lattice
structure filter (α:Type*) :=
(sets : set (set α))
(univ_sets : set.univ ∈ sets)
(sets_of_superset {X Y} : X ∈ sets → X ⊆ Y → Y ∈ sets)
(inter_sets {X Y} : X ∈ sets → Y ∈ sets → X ∩ Y ∈ sets)

namespace filter
universes u
variables {α : Type u} {ℱ 𝒢 : filter α} {X Y : set α}

instance : has_mem (set α) (filter α) := 
⟨λ X ℱ, X ∈ ℱ.sets⟩

lemma ext : ∀ {ℱ 𝒢 : filter α}, ℱ.sets = 𝒢.sets → ℱ = 𝒢
| ⟨s,_,_,_⟩ ⟨_,_,_,_⟩ rfl := rfl

def principal (X : set α) : filter α := 
⟨ {S | X ⊆ S}
, λ _ _, ⟨⟩
, λ _ _ hA ss _ ha, ss (hA ha)
, λ A B hA hB, subset.inter hA hB
⟩ 

instance : has_bot (filter α) := ⟨principal ∅⟩
instance : has_top (filter α) := ⟨principal univ⟩
 
/--Supremum of a filter of filters-/
def Join_filter (ℱ : filter (filter α)) : filter α :=
⟨ {S | {𝒢 : filter α | S ∈ 𝒢} ∈ ℱ}
,   suffices {𝒢 : filter α | set.univ ∈ 𝒢.sets} ∈ ℱ.sets, from this,
    by simp [filter.univ_sets]; exact ℱ.univ_sets
, λ A B hA ss, ℱ.sets_of_superset hA (λ 𝒢 gm, 𝒢.sets_of_superset gm ss)
, λ A B hA hB, sets_of_superset ℱ (inter_sets ℱ hA hB) (λ 𝒢 ⟨h₁, h₂⟩, inter_sets 𝒢 h₁ h₂)
⟩

instance : partial_order (filter α) :=
{ le := λ ℱ 𝒢, 𝒢.sets ⊆ ℱ.sets
, le_antisymm := λ _ _ h₁ h₂, filter.ext $ subset.antisymm h₂ h₁
, le_refl := λ a, subset.refl
, le_trans := λ a b c h₁ h₂, subset.trans h₂ h₁
}

lemma principal.monotone {X Y : set α} (ss : X ⊆ Y) : principal X ≤ principal Y := λ A hA, subset.trans ss hA

def forget : filter α → set (set α) := filter.sets

inductive free_gen (G : set (set α)) : set α → Prop
|basic {A} : A ∈ G → free_gen A
|univ {} : free_gen univ
|superset {A B} : free_gen A → A ⊆ B → free_gen B
|inter {A B} : free_gen A → free_gen B → free_gen (A ∩ B)

/-- Take the set of sets G and make the smallest filter which contains G. -/
def free (G : set (set α)) : filter α :=
{ sets := free_gen G
, univ_sets := free_gen.univ
, sets_of_superset := λ A B, free_gen.superset
, inter_sets := λ A B, free_gen.inter
}

variables {G : set (set α)}
lemma free.incl : ∀ A ∈ G, A ∈ free G :=
    λ A hA, free_gen.basic hA

lemma free.is_galois : (G ⊆ forget ℱ) ↔ ℱ ≤ free G :=
⟨λ ss X h, free_gen.rec_on h 
    (λ _ hX, ss hX) 
    (ℱ.univ_sets) 
    (λ A B _ ssA rec, ℱ.sets_of_superset rec ssA) 
    (λ A B _ _ r1 r2, ℱ.inter_sets r1 r2)
, λ l A hA, l $ free_gen.basic hA
⟩

lemma free.reflective : (free (forget ℱ)) = ℱ :=
    have l: (free (forget ℱ)) ≤ ℱ, from λ A hA, free_gen.basic hA,
    have r: (ℱ ≤ (free (forget ℱ))), from free.is_galois.1 subset.refl,
    partial_order.le_antisymm _ _ l r

instance : complete_lattice (filter α) := 
{ meet := λ ℱ 𝒢,
    {sets := {S | ∃ (A ∈ ℱ) (B ∈ 𝒢), A ∩ B ⊆ S}
    , univ_sets := ⟨univ, univ_sets _, univ, univ_sets _, λ x h, h.1⟩
    , sets_of_superset := λ X Y ⟨A, hA, B, hB, hi⟩ ss, ⟨A,hA,B,hB, subset.trans hi ss⟩
    , inter_sets := λ X Y ⟨XA, hXA, XB, hXB, iX⟩ ⟨YA, hYA, YB, hYB, iY⟩,
        ⟨XA ∩ YA, inter_sets _ hXA hYA, XB ∩ YB, inter_sets _ hXB hYB
        ,   calc (XA ∩ YA) ∩ (XB ∩ YB) = (XA ∩ XB) ∩ (YA ∩ YB) : by ac_refl
                                 ...   ⊆ X ∩ Y                 : subset.inter_subset_inter iX iY
        ⟩
    }
, π₁ := λ ℱ 𝒢 X h, ⟨X, h, univ, univ_sets _ ,λ x ⟨a,b⟩, a⟩
, π₂ := λ ℱ 𝒢 X h, ⟨univ, univ_sets _ , X, h, λ x ⟨a,b⟩, b⟩
, u_meet := λ (𝒜 ℬ 𝒞 : filter α) ab ac X ⟨B, hB, C, hC, ix⟩, sets_of_superset 𝒜 (inter_sets 𝒜 (ab hB) (ac hC)) ix

, join := λ ℱ 𝒢, free (forget ℱ ∩ forget 𝒢)
, ι₁ := λ ℱ 𝒢, free.is_galois.1 subset.π₁
, ι₂ := λ ℱ 𝒢, free.is_galois.1 subset.π₂
, u_join := λ 𝒜 ℬ 𝒞 ba ca A hA, free_gen.basic ⟨ba hA, ca hA⟩

, top := principal univ
, le_top := λ ℱ A hA, subset.antisymm hA subset.univ ▸ ℱ.univ_sets

, bot := principal ∅
, bot_le := λ ℱ A hA, subset.empty

, Join := λ fs, free $ {S | ∀ f ∈ fs, S ∈ f}
, ι := λ ℱs ℱ h₁, free.is_galois.1 (λ X h₂, h₂ ℱ h₁)
, u_Join := λ ℱs ℱ ts X h, free_gen.basic (λ ℱ h₂, ts _ h₂ h)

, Meet := λ fs, free $ {S | ∃ f ∈ fs, S ∈ f}
, π := λ ℱs ℱ h₁ X h₂, free_gen.basic $ ⟨ℱ, h₁, h₂⟩
, u_Meet := λ ℱs 𝒢 h₁, free.is_galois.1 (λ A ⟨ℱ,h₄,h₅⟩, h₁ ℱ h₄ h₅)

, ..filter.partial_order
}

variables {β : Type u}

instance : functor (filter) := 
{ map := λ α β m 𝒜, 
    { sets := {S | {x | m x ∈ S} ∈ 𝒜}
    , univ_sets := 𝒜.univ_sets
    , sets_of_superset := λ X Y h₁ ss, 𝒜.sets_of_superset h₁ (λ x h₂, ss h₂)
    , inter_sets := λ X Y h₁ h₂, 𝒜.inter_sets h₁ h₂
    }
}

instance : is_lawful_functor (filter) := 
{ id_map := λ α f, filter.ext rfl
, comp_map := λ α β γ g h 𝒜, filter.ext rfl
}

/-- An ultrafilter is a minimal filter. Adding any more sets will cause it to be the universe. -/
def ultrafilter := {ℱ : filter α // is_minimal ℱ}

def tendsto {β : Type u} (f : α → β) (𝒜 : filter α) (ℬ : filter β) := (f <$> 𝒜) ≤ ℬ

end filter



