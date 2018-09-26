

import .filter
open set filter lattice
universes u v w

class topology (α : Type u) :=
(𝒪 : set (set α))
(top : univ ∈ 𝒪)
(i : ∀ U V ∈ 𝒪, U ∩ V ∈ 𝒪)
(U : ∀ ℱ ⊆ 𝒪, ⋃₀ ℱ ∈ 𝒪)


namespace topology

variables {X : Type u} [topology X]
variables {Y : Type u} [topology Y]
lemma ext {X : Type u} : ∀ {τ₁ τ₂ : topology X}, @topology.𝒪 _ τ₁ = @topology.𝒪 _ τ₂ → τ₁ = τ₂
|⟨O,_,_,_⟩ ⟨_,_,_,_⟩ rfl := rfl
lemma has_empty : ∅ ∈ 𝒪(X) := 
    have s:(⋃₀ ∅ ∈ 𝒪(X)), from U ∅ (λ _ y,false.rec_on _ y),
    by rw <-union.empty; exact s
def is_open (U : set X) : Prop := U ∈ 𝒪(X)
def is_closed (V : set X) : Prop :=  (-V) ∈ 𝒪(X)
/--Set of closed subsets of topology X -/
def 𝒞 : set (set X) := {V | (-V) ∈ 𝒪(X)}

def nhds (x : X) : filter X := ⨅₀ (principal <$> {U|x ∈ U ∧ U ∈ 𝒪(X)})
lemma nhds_have_x {x : X} {U:set X} {h : U ∈ nhds x} : x ∈ U 
:= free_gen.rec_on h
    (λ V ⟨f,⟨W,⟨q,oW⟩,p⟩,j⟩ ,begin rw <-p at j, apply j q end) 
    (⟨⟩) 
    (λ A B _ ss xA, ss xA) 
    (λ A B _ _ xA xB,⟨xA,xB⟩)

def compact (S : set X) := ∀ℱ, ℱ ≠ ⊥ → ℱ ≤ principal S → ∃ s ∈ S, ℱ ⊓ nhds s ≠ ⊥
def hausdorff (X : Type u) [topology X] := ∀ u v : X, ∃ (U ∈ 𝒪(X)) (V ∈ 𝒪(X)), u ∈ U ∧ v ∈ V ∧ U ∩ V = ∅ 
instance (α : Type u) : partial_order (topology α) := 
{ le := λ X Y, @topology.𝒪 _ X ⊆ @topology.𝒪 _ Y
, le_refl := λ a, subset.refl
, le_trans := λ a b c ab bc, subset.trans ab bc
, le_antisymm := λ a b ab ba, topology.ext $ subset.antisymm ab ba
}
def indiscrete (α : Type u) : topology α := 
{ 𝒪 := {U|U = ∅ ∨ U = univ} 
, top := or.inr rfl
, i := λ U V hu hv, begin cases hu, all_goals{ cases hv}, all_goals {rw hu, rw hv}, repeat{apply or.inl inter.empty}, apply or.inl, rw inter_comm, apply inter.empty, exact (or.inr $ set.ext (λ z, ⟨λ ⟨a,_⟩, a, λ a, ⟨a,a⟩⟩)) end
, U := λ ℱ h₁, 
    or.rec_on (classical.em (univ ∈ ℱ)) 
        (λ h, or.inr $ set.ext $ (λ a, ⟨λ x, ⟨⟩,λ x, ⟨univ,h,x⟩⟩))
        (λ h, or.inl $ set.ext $ (λ a, ⟨λ ⟨U,h₂,h₃⟩, or.rec_on (h₁ h₂) (λ p, p ▸ h₃) (λ p, absurd h₂ (eq.symm p ▸ h) ), λ x, false.rec_on _ x⟩))
}
instance : has_initial (topology X) :=
{  bot := indiscrete X
,  bot_le := λ τ U oU, begin cases oU, rw oU, apply @has_empty, rw oU, apply top  end
}
def discrete (α : Type u) : topology α :=
{ 𝒪 := set.powerset univ
, top := λ _ _, ⟨⟩, i := λ _ _ _ _ _ _, ⟨⟩, U := λ _ _ _ _, ⟨⟩
}
instance : has_terminal (topology X) := 
{   top := discrete X
,   le_top := λ τ U oU u uX, trivial }
def is_lim (ℱ : filter X) (x : X) : Prop := ℱ ≤ nhds x
/-- The the topology of neighbourhoods on a filter -/
def free {X : Type u} (x : X) (ℱ : filter X) : topology X :=
{ 𝒪 := {U|x ∈ U → U ∈ ℱ}
, top := λ _, filter.univ_sets _
, i := λ A B fA fB i, filter.inter_sets _ (fA i.1) (fB i.2)
, U := λ 𝒢 f𝒢 ⟨G, GG, xG⟩, filter.sets_of_superset ℱ (f𝒢 GG xG) (λ y o, ⟨G,GG,o⟩)
} 
def is_galois {X : Type u} {x : X} {ℱ : filter X} (τ : topology X) : ℱ ≤ @nhds _ τ x ↔ τ ≤ free x ℱ :=
⟨
    assume l : ∀ U, U ∈ @nhds _ τ x → U ∈ ℱ,
    assume U (oU : U ∈ @𝒪 _ τ) (xU : x ∈ U), 
    l U $ free_gen.basic ⟨principal U, ⟨U,⟨xU,oU⟩,rfl⟩, λ _, id⟩
,   assume r : ∀ V, V ∈ @𝒪 X τ → x ∈ V → V ∈ ℱ,
    assume U nU, begin apply free.is_galois.mp _ nU, assume V h, cases h with f h₂, cases h₂ with h₂ h₃, cases h₂ with W h₄, cases h₄ with h₄ h₅,  cases h₄ with h₄ h₆, rw <- h₅ at *, clear h₅ f, apply filter.sets_of_superset ℱ, apply r, apply h₆, apply h₄, apply h₃,  end 
⟩
-- begin
--     apply iff.intro,
--     focus {
--         assume l U oU h,
--         apply l, apply filter.free_gen.basic, 
--         existsi (principal U), split, existsi U, split, split, assumption, assumption, refl, intro r, exact id
--     },
--     focus {
--         assume r U fU, apply r, cases fU,
--         focus {
--             cases fU_a with f h, 
--             cases h with h h₂, cases h with V h₄, cases h₄ with h₃ h₄, cases h₄, clear h₄, cases h₃ with h₃ h₅,
            
--         } 
--     }
-- end

def continuous {X Y : Type u} [topology X] [topology Y] (f : X → Y) := ∀ V ∈ 𝒪(Y), {x|f(x)∈V} ∈ 𝒪(X)
lemma continuous.id : continuous (id : X → X) := λ V oV, oV
lemma continuous.comp {X Y Z : Type u} [topology X] [topology Y] [topology Z] 
    {f : X → Y} {g : Y → Z} (cf : continuous f) (cg : continuous g) : continuous (g ∘ f)
:= λ V oV, cf _ (cg V oV)

def preimage {α : Type u} {β : Type v} (f : α → β) (s : set β) : set α := {x | f x ∈ s}

def induced {X Y : Type u} [topology Y] (f : X → Y) : topology X :=
{ 𝒪 := {U | ∃ V, V ∈ 𝒪(Y) ∧ {x|f(x)∈V} = U}
, top := ⟨univ,top Y,set.ext $ λ a, ⟨λ x, ⟨⟩,λ h, ⟨⟩⟩⟩
, U := λ ℱ,
    assume oℱ : ∀ U ∈ ℱ, ∃ (V : set Y), V ∈ 𝒪 Y ∧ {x : X | f x ∈ V} = U,
    let 𝒢 := {S ∈ 𝒪(Y)| ∃ (U ∈ ℱ), U = {x|f x ∈ S}} in
    let G := ⋃₀ 𝒢 in
    ⟨G, topology.U 𝒢 (λ S gS, gS.1)
    , set.ext $ λ x, 
        ⟨ begin 
            assume h : f x ∈ G,
            show x ∈ ⋃₀ ℱ,
            cases h with V h, cases h with h₁ h₂, cases h₁ with h₃ h₄, cases h₄ with U h₅, cases h₅ with h₅ h₆,
            existsi U, existsi h₅, rw h₆, exact h₂
          end
        , begin
            assume h : x ∈ ⋃₀ ℱ,
            show f x ∈ G,
            cases h with U h, cases h with h₁ h₂,
            have h₃ : ∃ (V : set Y), V ∈ 𝒪 Y ∧ {x : X | f x ∈ V} = U, from oℱ U h₁,
            cases h₃ with V h₃, cases h₃ with h₃ h₄,
            existsi V, split, split, exact h₃, simp, existsi U, existsi h₁, exact h₄,
            rw <-h₄ at h₂, exact h₂
        end 
        ⟩
    ⟩
, i := λ U V ⟨U',oU',pU'⟩ ⟨V',oV',pV'⟩, 
    ⟨U'∩V',topology.i _ _ oU' oV', 
    set.ext $ λ x, ⟨λ h, 
        begin rw [<-pU',<-pV'], split, exact h.1, exact h.2 end, λ h, 
        begin rw [<-pU',<-pV'] at h, exact h end⟩⟩ 
}





end topology