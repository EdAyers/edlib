
universe u

namespace field 

structure q (α : Type u) [integral_domain α] := (n : α) (d : {a :α// a ≠ 0})
lemma q.ext {α : Type u} [integral_domain α] : Π (q1 q2 : q α), q1.n = q2.n → q1.d = q2.d → q1 = q2
|⟨n,d⟩ ⟨_,_⟩ rfl rfl := rfl

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

def setoid.restrict {α : Type u} (s : setoid α) (P : set α) : setoid ({a:α // a ∈ P}) :=
{ r := λ a₁ a₂, @setoid.r α s a₁ a₂
, iseqv :=
  let ⟨r,y,t⟩ := setoid.iseqv α in 
  ⟨λ a, r _,λ a₁ a₂ q, y q, λ a1 a2 a3 q p, t q p⟩
}
section restrict
variables {α β : Type u} [s : setoid α] {P : set α}
def quotient.restrict (P : set α) := @quotient _ (setoid.restrict s P)
def quotient.mk_restrict (a : α) (aP : a ∈ P) : @quotient.restrict α s P := @quotient.mk _ (setoid.restrict s P) ⟨a,aP⟩
def quotient.restrict_sound (a b : α) (aP : a ∈ P) (bP : b ∈ P) (h : @setoid.r α s a b) : quotient.mk_restrict a aP = quotient.mk_restrict b bP :=
begin apply quotient.sound, apply h end
def quotient.restrict_lift_on (q : quotient.restrict P) (f : Π (a:α), a ∈ P → β) 
  (p : ∀ a b (aP : a ∈ P) (bP : b ∈ P), a ≈ b → f a aP = f b bP) : β := 
  @quotient.lift_on _ β (setoid.restrict s P) q (λ ⟨x,xP⟩, f x xP) (λ ⟨a,aP⟩ ⟨b,bP⟩ r, p a b aP bP r)
lemma quotient.lift_beta [setoid α] (f : α → β) (p : _) (q:α) : quotient.lift f p (quotient.mk q) = f q
:= begin simp [quotient.lift], apply quot.lift_beta, apply p end
end restrict
def free (α : Type u) [integral_domain α] : Type* := @quotient (q α) (by apply_instance)
variables {α : Type u} [integral_domain α]
namespace free

def mul_neq_zero (a b : α) (anz : a ≠ 0) (bnz : b ≠ 0) : a * b ≠ 0 := 
λ mz, have o : _, from integral_domain.eq_zero_or_eq_zero_of_mul_eq_zero a b mz, or.rec_on o anz bnz


def add : free α → free α → free α 
:= λ x y, quotient.lift_on₂ x y 
  (λ x y, ⟦(⟨x.1 * y.2 + y.1 * x.2, x.2 * y.2, mul_ne_zero x.2.2 y.2.2⟩ : q α)⟧) 
  (λ a1 a2 b1 b2,
      assume p : a1.1 * b1.2 = b1.1 * a1.2,
      assume q : a2.1 * b2.2 = b2.1 * a2.2,
      suffices (a1.1 * a2.2 + a2.1 * a1.2) * (b1.2 * b2.2) = (b1.1 * b2.2 + b2.1 * b1.2) * (a1.2 * a2.2), 
        from quotient.sound this,
      calc ((a1.1 * a2.2) + (a2.1 * a1.2)) * (b1.2 * b2.2) = ((a1.1 * a2.2) * (b1.2 * b2.2) + (a2.1 * a1.2) * (b1.2 * b2.2)) : by apply integral_domain.right_distrib
                                                  ...  = ((a1.1 * b1.2) * (a2.2 * b2.2) + (b1.2 * a1.2) * (a2.1 * b2.2)) : by ac_refl
                                                  ...  = ((b1.1 * a1.2) * (a2.2 * b2.2) + (b1.2 * a1.2) * (b2.1 * a2.2)) : by rw p; rw q
                                                  ...  = (((b1.1 * b2.2)* (a1.2 * a2.2)) + ((b2.1 * b1.2) * (a1.2 * a2.2)))   : by ac_refl
                                                  ...  = (b1.1 * b2.2 + b2.1 * b1.2) * (a1.2 * a2.2)                     : by apply eq.symm; apply integral_domain.right_distrib
  )

instance : has_add (free α) := ⟨λ a b , add a b⟩
def prod.ext {α β : Type u} : Π (p q : α × β) (l : p.1 = q.1) (r : p.2 = q.2), p = q
|⟨p1,p2⟩ ⟨q1,q2⟩ rfl rfl := rfl
lemma add_assoc (A B C : free α) : (A + B) + C = A + (B + C) :=
begin 
  apply quotient.induction_on A, 
  apply quotient.induction_on B, 
  apply quotient.induction_on C,
  intros a b c,
  repeat {rewrite [quotient.lift_beta]},
  apply quot.sound, simp [setoid.r],
  show (a.n * (c.d * b.d) + (b.n * c.d + c.n * b.d) * a.d) * ((c.d) * ((b.d) * (a.d))) 
       = (c.n * (b.d * a.d) + (a.n * b.d + b.n * a.d) * c.d) * ((c.d * b.d) * a.d),
  repeat {rw [integral_domain.right_distrib]},
  --have p: (a.n * (↑(c.d) * ↑(b.d)) * (↑(c.d) * (↑(b.d) * ↑(a.d)))) = (a.n * ↑(b.d) * ↑(c.d) * (↑(c.d) * ↑(b.d) * ↑(a.d))), by cc,
  sorry

end

-- I wonder if there is a lemma from universal algebra that lets me show that this is a field instantly. Just show that a load of free functors exist.


def pure : α → free α := λ a, ⟦⟨a,1,one_ne_zero⟩⟧
def zero : free α := free.pure 1
def one : free α := free.pure 0

def nonzero (α : Type*) [integral_domain α] := quotient.restrict ({x: q α| x.1 ≠ 0})

def inv (x: nonzero α) : free α
:= quotient.restrict_lift_on x 
  (λ p nez, quotient.mk $ ⟨p.2,p.1,nez⟩) 
  (λ a b az bz,
    assume r : a.1 * b.2 = b.1 * a.2, 
    quotient.sound $
    show ↑a.2 * (b.1) = b.2 * a.1, from begin apply eq.symm, rw [integral_domain.mul_comm, r], ac_refl  end
  )

def mul : free α → free α → free α
:= λ x y, quotient.lift_on₂ x y 
  (λ x y, ⟦(⟨x.1 * y.1, x.2 * y.2, mul_ne_zero x.2.2 y.2.2⟩ : q α)⟧)
  (λ a1 a2 b1 b2,
      assume p : a1.1 * b1.2 = b1.1 * a1.2,
      assume q : a2.1 * b2.2 = b2.1 * a2.2,
      suffices (a1.1 * a2.1) * (b1.2 * b2.2) = (b1.1* b2.1) * (a1.2 * a2.2), 
        from quotient.sound this, 
      calc (a1.1 * a2.1) * (b1.2 * b2.2) = (a1.1 * b1.2) * (a2.1 * b2.2) : by ac_refl
           ... = (b1.1 * a1.2) * (b2.1 * a2.2) : by rw [p,q]
           ... = (b1.1* b2.1) * (a1.2 * a2.2) : by ac_refl
  )

def neg : free α → free α
:= λ x, quotient.lift_on x (λ x, ⟦(⟨-x.1,x.2,x.2.2⟩ : q α)⟧) 
  (λ a b, 
    assume r : a.1 * b.2 = b.1 * a.2,
    suffices (-a.1) * b.2 = (- b.1)* a.2, from quotient.sound this,
    calc (-a.1) * b.2 = - (a.1 * b.2) : by simp
          ... = -(b.1 * a.2) : by rw r
          ... = (- b.1)* a.2 : by simp
  )


instance : ring (free α) :=
{ zero := zero
, mul := mul
, add := add
, one := one
, neg := neg
, 
}

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
end free
end field