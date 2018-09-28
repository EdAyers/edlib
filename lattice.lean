import .set
set_option old_structure_cmd true -- stops errors for diamonds.

universes u v

section
  variables {α : Type u} {ι : Type v} {a b c: α}
  /-- A function between preorders is monotone if
  `a ≤ b` implies `f a ≤ f b`. -/
  def monotone [preorder α] [preorder ι] (f : α → ι) := ∀⦃a b⦄, a ≤ b → f a ≤ f b

  reserve infixl ` ⊓ `:70
  reserve infixl ` ⊔ `:65

  instance [partial_order α] : has_coe (a = b) (a ≤ b) := ⟨le_of_eq⟩
  instance : has_coe (a = b) (b = a) := ⟨eq.symm⟩
  infixl ` ◾ ` : 300 := le_trans

  /-- Typeclass for the `⊔` (`\lub`) notation -/
  class has_join (α : Type u) := (join : α → α → α)
  /-- Typeclass for the `⊓` (`\glb`) notation -/
  class has_meet (α : Type u) := (meet : α → α → α)
  /-- Typeclass for the `⊤` (`\top`) notation -/
  class has_top (α : Type u) := (top : α)
  /-- Typeclass for the `⊥` (`\bot`) notation -/
  class has_bot (α : Type u) := (bot : α)

  notation `⊤` := has_top.top _
  notation `⊥` := has_bot.bot _
  infix ⊔ := has_join.join
  infix ⊓ := has_meet.meet

  class has_Join (α : Type u) := (Join : set α → α)
  class has_Meet (α : Type u) := (Meet : set α → α)

  def iJoin [has_Join α] (s : ι → α) : α := has_Join.Join {a : α | ∃i : ι, a = s i}
  def iMeet [has_Meet α] (s : ι → α) : α := has_Meet.Meet {a : α | ∃i : ι, a = s i}

  notation `⨆` binders `, ` r:(scoped f, iJoin f) := r
  prefix `⨆₀`:120 := has_Join.Join
  notation `⨅` binders `, ` r:(scoped f, iMeet f) := r
  prefix `⨅₀`:120 := has_Meet.Meet
end

variables (α : Type u) [partial_order α]
/-- Pairwise meets -/
class meet_semilattice extends has_meet α :=
(π₁ (a b : α) : a ⊓ b ≤ a)
(π₂ (a b : α) : a ⊓ b ≤ b)
(u_meet (a b c : α) : a ≤ b → a ≤ c → a ≤ b ⊓ c)

class has_terminal extends has_top α :=
(le_top (a : α) : a ≤ ⊤)

/--Setwise meets-/
class Meet_semilattice extends has_Meet α :=
(π : ∀s, ∀a∈s, Meet s ≤ a)
(u_Meet : ∀s a, (∀b∈s, a ≤ b) → a ≤ Meet s)
open Meet_semilattice


instance meet_of_Meet [Meet_semilattice α] : meet_semilattice α :=
{ meet := λ a b, ⨅₀ {a,b},
  π₁ := λ a b, π {a,b} a set.pair₁,
  π₂ := λ a b, π {a,b} b set.pair₂,
  u_meet := λ a b c ab ac, u_Meet {b,c} a (λ x h, or.rec_on h (λ p, ac ◾ p) (λ h₂, or.rec_on h₂ (λ p, ab ◾ p) (λ q, false.rec_on _ q))),
}

instance top_of_Meet [Meet_semilattice α] : has_terminal α :=
{ top := ⨅₀ ∅
, le_top := λ a, u_Meet ∅ a (λ b h, false.rec_on _ h)
}

class join_semilattice extends has_join α:=
(ι₁ (a b : α) : a ≤ a ⊔ b)
(ι₂ (a b : α) : b ≤ a ⊔ b)
(u_join (a b c : α) : b ≤ a → c ≤ a → b ⊔ c ≤ a)

class lattice extends meet_semilattice α, join_semilattice α 

class has_initial extends has_bot α :=
(bot_le (a : α) : ⊥ ≤ a)

class bounded_lattice extends lattice α, has_terminal α, has_initial α

class Join_semilattice extends has_Join α :=
(ι : ∀s, ∀a∈s, a ≤ Join s)
(u_Join : ∀s a, (∀b∈s, b ≤ a) → Join s ≤ a)

/-- A distributive lattice is a lattice that satisfies any of four
  equivalent distribution properties (of sup over inf or inf over sup,
  on the left or right). A classic example of a distributive lattice
  is the lattice of subsets of a set, and in fact this example is
  generic in the sense that every distributive lattice is realizable
  as a sublattice of a powerset lattice. -/
class distrib_lattice extends lattice α :=
(le_sup_inf : ∀x y z : α, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ (y ⊓ z))

/-- A lattice which has setwise joins and meets. You also must explicitly provide the meets and joins to make definitional equality nice. -/
class complete_lattice extends Meet_semilattice α, Join_semilattice α, meet_semilattice α, join_semilattice α, has_terminal α, has_initial α
open complete_lattice
def is_minimal [has_initial α]  (a : α) : Prop := ∀ b : α, b < a → b = ⊥
def is_maximal [has_terminal α]  (a : α) : Prop := ∀ b : α, a < b → b = ⊤

section order_dual
def order_dual (α : Type*) := α
instance (α : Type*) [has_le α] : has_le (order_dual α) := ⟨λ (x y : α), y ≤ x⟩
instance (α : Type*) [po : partial_order α] : partial_order (order_dual α) :=
{ le_refl := begin intros, apply le_refl end
, le_trans := begin intros, apply le_trans, assumption, assumption end
, le_antisymm := begin intros, apply @le_antisymm _ po, assumption, assumption end
, ..(order_dual.has_le α)
}
instance [x : has_meet α] : has_join (order_dual α) := ⟨(@has_meet.meet _ x : α → α → α)⟩
instance [x : has_join α] : has_meet (order_dual α) := ⟨(@has_join.join _ x : α → α → α)⟩
instance [x : has_top α] : has_bot (order_dual α) := ⟨(⊤ : α)⟩
instance [x : has_bot α] : has_top (order_dual α) := ⟨(⊥ : α)⟩
instance [x : has_Join α] : has_Meet (order_dual α) := ⟨(@has_Join.Join _ x : set α → α)⟩
instance [x : has_Meet α] : has_Join (order_dual α) := ⟨(@has_Meet.Meet _ x : set α → α)⟩

-- instance dual [po : partial_order α] [cl : complete_lattice α] : @complete_lattice (order_dual α) (@order_dual.partial_order α po) :=
-- { π₁ :=     @complete_lattice.ι₁     α po cl
-- , ι₁ :=     @complete_lattice.π₁     α po cl
-- , π₂ :=     @complete_lattice.ι₂     α po cl
-- , ι₂ :=     @complete_lattice.π₂     α po cl
-- , π :=      @complete_lattice.ι      α po cl
-- , ι :=      @complete_lattice.π      α po cl
-- , u_Meet := @complete_lattice.u_Join α po cl
-- , u_meet := @complete_lattice.u_join α po cl
-- , u_Join := @complete_lattice.u_Meet α po cl
-- , u_join := @complete_lattice.u_meet α po cl
-- , bot_le := @complete_lattice.le_top α po cl
-- , le_top := @complete_lattice.bot_le α po cl
-- , ..order_dual.has_bot
-- , ..order_dual.has_top
-- , ..order_dual.has_meet
-- , ..order_dual.has_join
-- , ..order_dual.has_Join
-- , ..order_dual.has_Meet
-- }
end order_dual