
universe u
inductive pred (α : Type u) : Type u
|and : pred → pred → pred
|not : pred → pred
|atom : α → pred

prefix `~` := pred.not
infixl `&`:50 := pred.and
def pred.or {α : Type u} : pred α → pred α  → pred α := λ P Q, ~((~P)&(~Q))
def pred.imp {α : Type u}: pred α  → pred α→ pred α  := λ P Q, ~(P&(~Q))
infixl `|`:40 := pred.or
local infixl `⊃`:50 := pred.imp
instance atom_coe {α} : has_coe (α) (pred α) := ⟨pred.atom⟩
section
parameter {α : Type u}
abbreviation p := pred α

end