import .set
section
universe u

def rel (α : Type u) := set (α × α)
variable {α : Type u}
instance rel_has_mem : has_mem (α × α) (rel α) := set.has_mem
instance rel_has_inter : has_inter (rel α) := set.has_inter
instance rel_has_union : has_union (rel α) := set.has_union
instance rel_has_subset : has_subset (rel α) := set.has_subset

def comp : rel α  → rel α → rel α 
|t s := {p | ∃ b:α, (p.1,b) ∈ t ∧ (b,p.2) ∈ s}

local infix `∙`:100 := comp 

variables {s t r : rel α }

theorem comp.assoc : s ∙ (t ∙ r) = (s ∙ t) ∙ r := 
set.ext $ λ ⟨a,z⟩, ⟨λ ⟨b,h₁,⟨y,h₂,h₃⟩⟩, ⟨y,⟨b,h₁,h₂⟩,h₃⟩, λ ⟨y,⟨b,h₁,h₂⟩,h₃⟩, ⟨b,h₁,⟨y,h₂,h₃⟩⟩⟩

theorem T59b : r ∙ (s ∩ t) ⊆ r ∙ s := λ ⟨a,z⟩ ⟨b,h₁,⟨h₃,h₄⟩⟩, ⟨b,_,h₃⟩

end

