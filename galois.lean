import .lattice
universes u
variables {α β : Type u}


section
variables [preorder α] [preorder β]
/-- A Galois connection is a pair of functions `l` and `u` satisfying
  `l a ≤ b ↔ a ≤ u b`. They are closely connected to adjoint functors
  in category theory. -/
def galois_connection 
  (l : α → β) (u : β → α) := ∀ a b, l a ≤ b ↔ a ≤ u b
structure galois_insertion (l : α → β) (u : β → α)  :=
--(choice : Πa:α, u (l a) ≤ a → β)
(gc : galois_connection l u)
(le_l_u : ∀ b:β, b ≤ l(u b))
--(choice_eq : ∀ a h, choice a h = l a)
end

variables [partial_order α] [partial_order β]
variables {l : α → β} {u : β → α}
lemma monotone_l (gc : galois_connection l u) : monotone l := λ a b q, begin apply (gc _ _).mpr, transitivity, apply q, apply (gc _ _).mp, reflexivity end
lemma monotone_u (gc : galois_connection l u) : monotone u := λ a b q, begin apply (gc _ _).mp, transitivity, apply (gc _ _).mpr, reflexivity, apply q end

def Meet_of_gi (gi : galois_insertion l u) [ms : Meet_semilattice α] : Meet_semilattice β :=
{ Meet := λ B, l (⨅₀ (set.image u B))
, π := λ B b bB, (gi.gc _ _).mpr $ Meet_semilattice.π _ _ $ ⟨b, bB, rfl⟩
, u_Meet := λ B b h, (gi.le_l_u _) ◾ (monotone_l gi.gc $ Meet_semilattice.u_Meet _ _ $ λ a ⟨g,h₁,h₂⟩, h₂ ▸ monotone_u gi.gc (h _ h₁))
}

def meet_of_gi (gi : galois_insertion l u) [ms : meet_semilattice α] : meet_semilattice β :=
{ meet := λ b₁ b₂, l (u b₁ ⊓ u b₂)
, π₁ := λ b₁ b₂, (gi.gc _ _).mpr $ meet_semilattice.π₁ _ _
, π₂ := λ b₁ b₂, (gi.gc _ _).mpr $ meet_semilattice.π₂ _ _
, u_meet := λ b b₁ b₂ h₁ h₂, (gi.le_l_u _) ◾ (monotone_l gi.gc $ meet_semilattice.u_meet _ _ _ (monotone_u gi.gc h₁) (monotone_u gi.gc h₂))
}

def join_of_gi (gi :galois_insertion l u) [js : join_semilattice α] : join_semilattice β :=
{ join := λ b₁ b₂, l (u b₁ ⊔ u b₂)
, ι₁ := λ b₁ b₂, (gi.le_l_u _) ◾ (monotone_l gi.gc $ join_semilattice.ι₁ _ _)
, ι₂ := λ b₁ b₂, (gi.le_l_u _) ◾ (monotone_l gi.gc $ join_semilattice.ι₂ _ _)
, u_join := λ b b₁ b₂ h₁ h₂, (gi.gc _ _ ).mpr $ join_semilattice.u_join _ _ _ (monotone_u gi.gc h₁) (monotone_u gi.gc h₂)
}

def Join_of_gi (gi : galois_insertion l u) [js : Join_semilattice α] : Join_semilattice β :=
{ Join := λ B, l (⨆₀ (set.image u B))
, ι := λ B b bB, (gi.le_l_u _) ◾ (monotone_l gi.gc $ Join_semilattice.ι _ _ ⟨_,bB,rfl⟩)
, u_Join := λ B b h, (gi.gc _ _).mpr $ Join_semilattice.u_Join _ _ $ λ b' ⟨a,aA,p⟩, p ▸ (monotone_u gi.gc $ h _ aA)
}

def initial_of_gi (gi : galois_insertion l u) [has_initial α] : has_initial β :=
{ bot := l (⊥)
, bot_le := λ b, (gi.gc _ _).mpr (has_initial.bot_le _)
}

def terminal_of_gi (gi : galois_insertion l u) [has_terminal α] : has_terminal β :=
{ top := l (⊤)
, le_top := λ b, (gi.le_l_u _) ◾ (monotone_l gi.gc $ has_terminal.le_top _)
}

def complete_lattice_of_gi (gi : galois_insertion l u) [complete_lattice α] : complete_lattice β :=
{ ..(Meet_of_gi gi)
, ..(Join_of_gi gi)
, ..(meet_of_gi gi)
, ..(join_of_gi gi)
, ..(initial_of_gi gi)
, ..(terminal_of_gi gi)
}