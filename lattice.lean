set_option old_structure_cmd true -- stops errors for diamonds.
universes u v
variables {α : Type u} {ι : Type v}
reserve infixl ` ⊓ `:70
reserve infixl ` ⊔ `:65

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

/-- Pairwise meets -/
class meet_semilattice (α : Type u) extends has_meet α, partial_order α :=
(π₁ (a b : α) : a ⊓ b ≤ a)
(π₂ (a b : α) : a ⊓ b ≤ b)
(u_meet (a b c : α) : a ≤ b → a ≤ c → a ≤ b ⊓ c)

/--Setwise meets-/
class Meet_semilattice (α : Type u) extends has_Meet α, partial_order α :=
(π : ∀s, ∀a∈s, Meet s ≤ a)
(u_Meet : ∀s a, (∀b∈s, a ≤ b) → a ≤ Meet s)

class join_semilattice (α : Type u) extends has_join α, partial_order α :=
(ι₁ (a b : α) : a ≤ a ⊔ b)
(ι₂ (a b : α) : b ≤ a ⊔ b)
(u_join (a b c : α) : b ≤ a → c ≤ a → b ⊔ c ≤ a)

class lattice (α : Type u) extends meet_semilattice α, join_semilattice α 

class has_terminal (α : Type u) extends has_top α, partial_order α :=
(le_top (a : α) : a ≤ ⊤)

class has_initial (α : Type u) extends has_bot α, partial_order α :=
(bot_le (a : α) : ⊥ ≤ a)

class bounded_lattice (α : Type u) extends lattice α, has_terminal α, has_initial α

class complete_lattice (α : Type u) extends bounded_lattice α, has_Join α, has_Meet α :=
(ι : ∀s, ∀a∈s, a ≤ Join s)
(u_Join : ∀s a, (∀b∈s, b ≤ a) → Join s ≤ a)




/-- A distributive lattice is a lattice that satisfies any of four
  equivalent distribution properties (of sup over inf or inf over sup,
  on the left or right). A classic example of a distributive lattice
  is the lattice of subsets of a set, and in fact this example is
  generic in the sense that every distributive lattice is realizable
  as a sublattice of a powerset lattice. -/
class distrib_lattice α extends lattice α :=
(le_sup_inf : ∀x y z : α, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ (y ⊓ z))





