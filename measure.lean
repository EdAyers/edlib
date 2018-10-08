
import .set .galois .lattice
universes u

variables {E : Type u}

def seq : Type u → Type u := λ α, ℕ → α

class σ_algebra {E : Type u} (ℰ : set (set E)) : Prop :=
(empty : ∅ ∈ ℰ)
(compl : ∀ A ∈ ℰ, -A ∈ ℰ)
(union : ∀ (As : ℕ → set E) (p : ∀ n, As n ∈ ℰ), (⋃ n, As n) ∈ ℰ)


namespace σ_algebra
    variables {ℰ : set (set E)} [σ_algebra ℰ]
    lemma inter : ∀ (As : ℕ → set E) (p : ∀ n, As n ∈ ℰ), (⋂ n, As n) ∈ ℰ :=
    begin
        intros As p,simp [set.Inter_compl], apply σ_algebra.compl, apply σ_algebra.union, 
        intro n, apply σ_algebra.compl, apply p,
    end

    def algebra_on (E : Type u) : Type* := {ℰ:set(set E) // σ_algebra ℰ}
    instance : has_mem (set E) (algebra_on E) := ⟨λ a b, a ∈ b.val⟩
    lemma ext : Π {ℰ₁ ℰ₂ : algebra_on E}, ℰ₁.val =  ℰ₂.val → ℰ₁ = ℰ₂
    |⟨_,_⟩ ⟨_,_⟩ rfl := rfl

    instance : partial_order (algebra_on E) :=
    { le := λ ℰ₁ ℰ₂, ℰ₁.1 ⊆ ℰ₂.1 
    , le_refl := λ ℰ A, id
    , le_trans := λ A B C, set.subset.trans
    , le_antisymm := λ A B l r, ext $ set.subset.antisymm l r
    }

    def forget : (algebra_on E) → set (set E) := λ x, x.val

    inductive gen_free (𝒜 : set (set E)) : set E → Prop
    |basic : ∀ A ∈ 𝒜, gen_free A
    |empty : gen_free ∅
    |compl : ∀ A, gen_free A → gen_free (-A)
    |union : ∀ (As : seq (set E)), (∀ n, gen_free (As n)) → gen_free (⋃ n, As n)

    def free (𝒜 : set (set E)) : algebra_on E := ⟨set_of $ gen_free 𝒜, {empty := gen_free.empty _,compl := gen_free.compl,union := gen_free.union}⟩

    def gc : @galois_connection (set (set E)) (algebra_on E) _ _ free forget :=
    λ 𝒜 ℰ,
    ⟨λ (h₁ : (free 𝒜).val ⊆ ℰ.val) A AA, h₁ (gen_free.basic A AA)
    ,λ (h₁ : 𝒜 ⊆ ℰ.val) A h₂, 
        have ecu : σ_algebra ℰ.val, from ℰ.2,
        gen_free.rec_on h₂ (λ B BE, h₁ BE) (ecu.empty) (λ B _ BE, @σ_algebra.compl _ _ ecu B BE) (λ As _ q, @σ_algebra.union _ _ ecu As q) 
    ⟩

    def gi : @galois_insertion (set (set E)) (algebra_on E) _ _ free forget :=
    { gc := gc
    , le_l_u := λ ℰ A mA, gen_free.basic A mA
    }
    instance : complete_lattice (algebra_on E) := complete_lattice_of_gi gi
    
    structure π_system (𝒜 : set (set E)) :=
    (empty : ∅ ∈ 𝒜)
    (inter : ∀ (A B ∈ 𝒜), A ∩ B ∈ 𝒜)

    structure d_system (𝒜 : set (set E)) :=
    (univ : set.univ ∈ 𝒜)
    (subs : ∀ (A B ∈ 𝒜), A ⊆ B → (B ∩ -A) ∈ 𝒜)
    (union : ∀ (f : seq (set E)), (∀ n, f n ∈ 𝒜) → (monotone f) → (⋃ n, f n) ∈ 𝒜)

    lemma dynkin {𝒜 𝒟 : set (set E)} (p: π_system 𝒜) (d : d_system 𝒟) (ss : 𝒜 ⊆ 𝒟) : (forget (free 𝒜) ⊆ 𝒟) :=
        let 𝒟' := { B ∈ 𝒟 |∀ A ∈ 𝒜, B ∩ A ∈ 𝒟} in
        have h₁ : 𝒜 ⊆ 𝒟', from λ A mA, ⟨ss mA,λ X mX, ss (p.inter _ _ mA mX)⟩,
        have h₂ : set.univ ∈ 𝒟', from ⟨d.univ, λ A mA, begin apply ss, rw set.inter.univ, apply mA end⟩,
        have h₃ : ∀ (B₁ B₂ ∈ 𝒟'), B₁ ⊆ B₂ → B₂ ∩ -B₁ ∈ 𝒟', from λ B₁ B₂ ⟨m1,h1⟩ ⟨m2,h2⟩ sb, 
            ⟨d.subs _ _ m1 m2 sb
            , λ A mA, 
                have h₄ : (B₂ ∩ -B₁) ∩ A = (B₂ ∩ A) ∩ -(B₁ ∩ A), from set.ext $ λ x, ⟨λ ⟨⟨i,j⟩,k⟩, ⟨⟨i,k⟩,λ ⟨l,m⟩, j l⟩,λ ⟨⟨i,j⟩,f⟩, ⟨⟨i,λ k, f⟨k,j⟩⟩,j⟩⟩ ,
                have h₅ : (B₂ ∩ A) ∈ 𝒟, from h2 A mA,
                have h₆ : (B₁ ∩ A) ∈ 𝒟, from h1 A mA,
                suffices (B₂ ∩ A) ∩ -(B₁ ∩ A) ∈ 𝒟, by simp [h₄, this],
                d.subs _ _ h₆ h₅ (λ x ⟨m2,ma⟩, ⟨sb m2, ma⟩)
            ⟩,
        have h₄: ∀ (f : seq (set E)), (∀ n, f n ∈ 𝒟') →(monotone f) → (⋃ n, f n) ∈ 𝒟', from 
            λ f p m, ⟨d.union (f) (λ n, (p n).1) m, λ A mA,
                have h₅ : (⋃ n, f n) ∩ A = (⋃ n, (f n) ∩ A), from set.ext $ λ x, ⟨λ ⟨⟨i,j⟩,k⟩, ⟨i,⟨j,k⟩⟩,λ ⟨i,⟨j,k⟩⟩, ⟨⟨i,j⟩,k⟩⟩,
                suffices (⋃ n, (f n) ∩ A) ∈ 𝒟, by simp [h₅, this],
                d.union _ (λ n, (p n).2 A mA) (λ i j ij x ⟨p,q⟩, ⟨m ij p,q⟩)
            ⟩,
        λ A mA, gen_free.rec_on mA 
            (λ A mA, ss mA) 
            (ss p.empty) 
            (λ B _ mB,
                suffices set.univ ∩ -B ∈ 𝒟, by simp [set.inter.univ] at this; assumption,
                d.subs B set.univ mB (d.univ) (λ _ _, ⟨⟩)
            )
            (λ f _ q, _)
        

end σ_algebra

--def disjoint_sequence (ℰ : set (set E)) := {As:ℕ→set E//(∀ n, As n ∈ ℰ) ∧ (∀ n m, As n ∩ As m = ∅)}

