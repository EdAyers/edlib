import .set
set_option old_structure_cmd true -- stops errors for diamonds.

universes u v

section
  variables {α : Type u} {ι : Type v} {a b c: α}
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

class Join_semilattice extends bounded_lattice α, has_Join α, has_Meet α :=
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

/-- A lattice which has setwise joins and meets -/
class complete_lattice extends Meet_semilattice α, Join_semilattice α, meet_semilattice α, join_semilattice α, has_terminal α, has_initial α

def is_minimal [has_initial α]  (a : α) : Prop := ∀ b : α, b < a → b = ⊥
def is_maximal [has_terminal α]  (a : α) : Prop := ∀ b : α, a < b → b = ⊤

