/- Combinatorics on lists. Copied from mathlib. -/


namespace list
universes u v
variables {α : Type u} {β : Type v}
inductive perm : list α → list α → Prop
|nil {}: perm [] [] 
|skip {x : α} {l₁ l₂ : list α} : perm l₁ l₂ → perm (x :: l₁) (x :: l₂)
|swap {x y : α} {l : list α} : perm (y::x::l) (x::y::l)
|trans {l₁ l₂ l₃ : list α} : perm l₁ l₂ → perm l₂ l₃ → perm l₁ l₃
open perm
infix ~ := perm

@[refl] protected theorem perm.refl : ∀ (l : list α), l ~ l
|[] := perm.nil
|(h::t) := skip $ perm.refl t

@[symm] protected theorem perm.symm : ∀ {l₁ l₂ : list α}, l₁ ~ l₂ → l₂ ~ l₁
:= λ l₁ l₂ p, perm.rec_on p (perm.nil) (λ x l₁ l₂ p q, skip q) (λ x y l, swap) (λ l₁ l₂ l₃ p₁₂ p₂₃ p₂₁ p₃₂, trans p₃₂ p₂₁)

attribute [trans] perm.trans

local infix ` ◾ ` :30 := perm.trans 
/- ...etc etc -/
end list


namespace perm
open nat
inductive fin : ℕ → Type
| zero {n} : fin (succ n)
| succ {n} : fin n → fin (succ n)

def fin_0_absurd {C : Type} : fin 0 → C :=
λ z, @fin.rec_on (λ n f, nat.rec_on n C (λ _ _, unit)) 0 z (λ x,⟨⟩) (λ x y g, ⟨⟩)

def fin.comp : Π {n m : ℕ}, fin n → fin m → ordering
|(succ n) (succ m) (fin.zero) (fin.zero) := ordering.eq
|(succ n) (succ m) (fin.succ x) (fin.zero) := ordering.gt
|(succ n) (succ m) (fin.zero) (fin.succ y) := ordering.lt
|(succ n) (succ m) (fin.succ x) (fin.succ y) := fin.comp x y

def fin.inj : Π {n : ℕ}, fin n → fin (succ n)
|(succ n) (fin.zero) := fin.zero
|(succ n) (fin.succ x) := fin.succ (fin.inj x)

universes u
inductive vec (α : Type u) : ℕ → Type u
|zero {} : vec 0
|cons {n} : α → vec n → vec (succ n)

def vec.popn {α : Type u} : Π {n:ℕ} (i:fin (succ n)), vec α (succ n) → α × vec α ( n)
|n (fin.zero) (vec.cons h t) := ⟨h,t⟩
|(succ n) (fin.succ i) (vec.cons h t) :=
    let ⟨a,t'⟩ := vec.popn i t in 
    ⟨a, vec.cons h t'⟩

inductive perm : ℕ → ℕ → Type
| first {n} :  perm 0 n
| pick {r n} : fin (succ n) → perm r n →  perm (succ r) (succ n)

infix ` ↪ `:40 := perm

def perm.id : Π {r}, r ↪ r
|0 := perm.first
|(succ r) := perm.pick (fin.zero) (perm.id)

def perm.empty_motive : ℕ → ℕ → Type
|0 n := unit
|(succ r) (succ n) := unit
|_ _ := empty

def perm.absurd : Π {r}, (succ r) ↪ 0 → empty
:= λ r π, @perm.rec_on (λ r n π, perm.empty_motive r n) (succ r) (0) π (λ n, ⟨⟩) (λ r n x y z, ⟨⟩)

def perm.inj : Π {r n}, r ↪ n → r ↪ (succ n)
|_ _ (perm.first) := perm.first 
|_ _ (perm.pick i π) := perm.pick (fin.inj i) (perm.inj π)

def perm.inj_at : Π {r n}, r ↪ n → fin (succ n) → r ↪ (succ n)
|_ _ (perm.first) _ := perm.first
|_ _ (perm.pick i π) (fin.zero) := perm.pick (fin.succ i) (perm.inj_at π fin.zero)
|_ _ (perm.pick (fin.zero) π) (fin.succ x) := perm.pick (fin.zero) (perm.inj_at π x)
|_ _ (perm.pick (fin.succ y) π) (fin.succ x) :=

-- def perm.get : Π {r n}, r ↪ n → fin r → fin n
-- --|r n (perm.first) z := 
-- |r n (perm.pick i π) (fin.zero) := i
-- |r n (perm.pick i π) (fin.succ x) :=
--     let j := perm.get π x in
--     match fin.comp i j with
--     |ordering.lt := fin.in

def perm.pop :Π {r n}, (succ r) ↪ (succ n) → fin (succ r) → fin (succ n) × r ↪ (succ n)
|r n (perm.pick i π) (fin.zero)  := ⟨i, perm.inj π⟩
|(succ r) (succ n) (perm.pick (fin.zero) π) (fin.succ x) :=



def perm.comp : Π {a b c}, a ↪ b → b ↪ c → a ↪ c
|0 _ _ _ _ := perm.first
|(succ a) 0 c π (perm.first) := empty.rec_on _ $ perm.absurd π
|(succ a) (succ b) 0 π₁ π₂ := empty.rec_on _ $ perm.absurd π₂
|(succ a) (succ b) (succ c) (perm.pick i₁ π₁) (perm.pick i₂ π₂) := _

def action {α : Type*} : Π {r n : ℕ}, perm r n → vec α n → vec α r
|_ _ (perm.first) v := vec.zero
|_ _ (perm.pick i π) v :=
    let ⟨a,t'⟩ := vec.popn i v in 
    vec.cons a (action π t')

end perm

#check fin
universes u

structure iso (n m : ℕ) :=
(f : fin n → fin m)
(g : fin m → fin n) 
(fg := f ∘ g = id)
(gf := g ∘ f = id)

def iso_inv {X} {Y} : iso X Y → iso Y X := λ ⟨f,g,fg,gf⟩, ⟨g,f,gf,fg⟩

infix ` ↭ `: 40 := iso
instance {X} {Y} : has_coe_to_fun (X ↭ Y) := ⟨λ F, fin X → fin Y, λ F, F.f⟩

postfix `⁻¹ ` := iso_inv

structure inj (r n : ℕ) : Type :=
(f : fin r → fin n)
(is_inj : ∀ x y, f x = f y → x = y)

infix ` ↪ `:40 := inj
instance {n r} : has_coe_to_fun (r ↪ n) := ⟨λ F, fin r → fin n, λ F, F.f⟩

def permuatation (r n : ℕ) := inj r n

def same_image {r} {n} : (r ↪ n) → (r ↪ n) → Prop :=
λ π₁ π₂, ∃ σ: r ↭ r, π₁ ∘ σ = π₂

/- something like; quotient inj by ordering? -/
def combination (r n : ℕ) := @quot (r ↪ n) same_image

inductive permuatation_concrete (r n : ℕ) := 

