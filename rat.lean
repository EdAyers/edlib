
universe u

namespace field 

structure q (α : Type u) [integral_domain α] := (n : α) (d : α ) (nz : d ≠ 0)
lemma q.ext {α : Type u} [integral_domain α] : Π (q1 q2 : q α), q1.n = q2.n → q1.d = q2.d → q1 = q2
|⟨n,d,nz⟩ ⟨_,_,_⟩ rfl rfl := rfl

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
  (λ x y, ⟦(⟨x.1 * y.2 + y.1 * x.2, x.2 * y.2, mul_ne_zero x.nz y.nz⟩ : q α)⟧) 
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

def neg : free α → free α
:= λ x, quotient.lift_on x (λ x, ⟦(⟨-x.1,x.2,x.nz⟩ : q α)⟧) 
  (λ a b, 
    assume r : a.1 * b.2 = b.1 * a.2,
    suffices (-a.1) * b.2 = (- b.1)* a.2, from quotient.sound this,
    by simp [r]
  )
instance : has_neg (free α) := ⟨neg⟩

instance : has_add (free α) := ⟨λ a b , add a b⟩
def prod.ext {α β : Type u} : Π (p q : α × β) (l : p.1 = q.1) (r : p.2 = q.2), p = q
|⟨p1,p2⟩ ⟨q1,q2⟩ rfl rfl := rfl

--
lemma add_assoc (A B C : free α) : (A + B) + C = A + (B + C) :=
begin 
  apply quotient.induction_on A, 
  apply quotient.induction_on B, 
  apply quotient.induction_on C,
  intros a b c,
  apply quot.sound, simp [setoid.r],
  show (a.n * (c.d * b.d) + (b.n * c.d + c.n * b.d) * a.d) * ((c.d) * ((b.d) * (a.d))) 
       = (c.n * (b.d * a.d) + (a.n * b.d + b.n * a.d) * c.d) * ((c.d * b.d) * a.d),
  repeat {rw [integral_domain.right_distrib]},
  generalize ah₁ : (a.n * (c.d * b.d) * (c.d * (b.d * a.d))) = a₁,
  generalize ah₂: a.n * b.d * c.d * (c.d * b.d * a.d) = a₂,
  generalize bh₁: b.n * c.d * a.d * (c.d * (b.d * a.d)) = b₁,
  generalize bh₂: b.n * a.d * c.d * (c.d * b.d * a.d) = b₂,
  generalize ch₁: c.n * b.d * a.d * (c.d * (b.d * a.d)) = c₁,
  generalize ch₂: c.n * (b.d * a.d) * (c.d * b.d * a.d) = c₂,
  have p : a₁ = a₂, by rw [<-ah₁, <-ah₂]; ac_refl,
  have q : b₁ = b₂, by rw [<-bh₁, <-bh₂]; ac_refl,
  have r : c₁ = c₂, by rw [<-ch₁, <-ch₂]; ac_refl,
  rw [p,q,r],
  ac_refl
end

def pure : α → free α := λ a, ⟦⟨a,1,one_ne_zero⟩⟧
def zero : free α := free.pure 0
def one : free α := free.pure 1

lemma zero_add (A : free α) : free.zero + A = A :=
begin
  apply quotient.induction_on A,
  intros a,
  apply quot.sound, 
  simp [setoid.r],
end

lemma add_comm (A B : free α) : A + B = B + A :=
begin 
  apply quotient.induction_on₂ A B, intros a b, apply quot.sound, simp [setoid.r],
  repeat {rw [integral_domain.right_distrib]},
  cc
end

lemma add_zero (A : free α) : A + free.zero = A := by rw [add_comm]; apply zero_add 

def nonzero (α : Type*) [integral_domain α] := quotient.restrict ({x: q α| x.1 ≠ 0})

def inv_guard (x: nonzero α) : free α
:= quotient.restrict_lift_on x 
  (λ p nez, quotient.mk $ ⟨p.2,p.1,nez⟩) 
  (λ a b az bz,
    assume r : a.1 * b.2 = b.1 * a.2, 
    quotient.sound $
    show a.d * (b.n) = b.d * a.n, from begin apply eq.symm, rw [integral_domain.mul_comm, r], ac_refl  end
  )

def mul : free α → free α → free α
:= λ x y, quotient.lift_on₂ x y 
  (λ x y, ⟦(⟨x.1 * y.1, x.2 * y.2, mul_ne_zero x.nz y.nz⟩ : q α)⟧)
  (λ a1 a2 b1 b2,
      assume p : a1.1 * b1.2 = b1.1 * a1.2,
      assume q : a2.1 * b2.2 = b2.1 * a2.2,
      suffices (a1.1 * a2.1) * (b1.2 * b2.2) = (b1.1* b2.1) * (a1.2 * a2.2), 
        from quotient.sound this, 
      calc (a1.1 * a2.1) * (b1.2 * b2.2) = (a1.1 * b1.2) * (a2.1 * b2.2) : by ac_refl
           ... = (b1.1 * a1.2) * (b2.1 * a2.2) : by rw [p,q]
           ... = (b1.1* b2.1) * (a1.2 * a2.2) : by ac_refl
  )
instance : has_mul (free α) := ⟨mul⟩
def mul_comm (A B : free α) : A * B = B * A :=
begin
  apply quotient.induction_on₂ A B, intros a b, apply quot.sound, simp [setoid.r], ac_refl
end
def mul_assoc (A B C : free α) : (A * B )* C = A * (B * C) :=
begin
  apply quotient.induction_on₂ A B, intros a b, apply quotient.induction_on C, intro c, apply quot.sound, simp [setoid.r], ac_refl
end
#check field.add_left_neg
lemma add_left_neg (A : free α) : (-A) + A = free.zero := begin
  apply quotient.induction_on A, intros a, apply quot.sound, simp [setoid.r],
  repeat {rw [integral_domain.right_distrib]},
  end

  lemma add_right_neg (A : free α) : (A) + (-A) = free.zero := begin
  apply quotient.induction_on A, intros a, apply quot.sound, simp [setoid.r],
  repeat {rw [integral_domain.right_distrib]},
  end

lemma one_mul (A : free α) : free.one * A = A := begin
  apply quotient.induction_on A, intros a, apply quot.sound, simp [setoid.r],
end
lemma mul_one (A : free α) :  A * free.one = A := begin
  apply quotient.induction_on A, intros a, apply quot.sound, simp [setoid.r],
end

#check congr_arg
def congr_arg2 {α β γ : Type*} {f : α → β → γ} : ∀ {a₁ a₂ : α} {b₁ b₂ : β} , (a₁ = a₂) → (b₁ = b₂) → f a₁ b₁ = f a₂ b₂
|_ _ _ _ rfl rfl := rfl

lemma right_distrib (A B C : free α) : (A + B) * C = A * C + B * C :=
begin 
  apply quotient.induction_on A, 
  apply quotient.induction_on B, 
  apply quotient.induction_on C,
  intros a b c,
  apply quot.sound, simp [setoid.r],
  repeat {rw [integral_domain.right_distrib]},
  --rw [integral_domain.add_comm],
  apply congr_arg2,
  ac_refl,
ac_refl
end

#eval 1 + 2 

lemma left_distrib (A B C : free α) : A * ( B + C) = A * B + A * C :=
begin 
  apply quotient.induction_on A, 
  apply quotient.induction_on B, 
  apply quotient.induction_on C,
  intros a b c,
  apply quot.sound, simp [setoid.r],
  repeat {rw [integral_domain.right_distrib]},
  repeat {rw [integral_domain.left_distrib]},
  repeat {rw [integral_domain.right_distrib]},
  --rw [integral_domain.add_comm],
  apply congr_arg2,
  ac_refl, ac_refl
end


instance : comm_ring (free α) :=
{ zero := zero
, mul := mul
, add := add
, one := one
, neg := neg
, add_assoc := add_assoc
, zero_add := zero_add
, add_zero := add_zero
, add_comm := add_comm
, mul_comm := mul_comm
, mul_assoc := mul_assoc
, add_left_neg := add_left_neg
, one_mul:=one_mul
, mul_one:=mul_one
, right_distrib:=right_distrib
, left_distrib:=left_distrib
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