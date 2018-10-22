
namespace list
    universes u
    variables {α : Type u} {l l₁ l₂: list α} {a : α}

    @[simp] lemma rev_nil : @list.reverse α [] = [] := begin unfold reverse, unfold reverse_core end
    @[simp] lemma rev_core_nil : reverse_core [] l = l := rfl
    @[simp] lemma rev_core_cons : reverse_core (a::l₁) l = reverse_core l₁ (a::l) := rfl

    @[simp] lemma rev_core_length : (list.length $ list.reverse_core l₁ l₂) = (list.length l₁) + (list.length l₂) :=
        @well_founded.recursion 
            (list α) 
            _
            (measure_wf (length)) 
            (λ l₁, ∀ l₂, (list.length $ list.reverse_core (l₁) l₂) = (list.length (l₁)) + (list.length l₂))
            (l₁)
            (λ l₃,
                list.rec_on l₃ (by simp) (λ h l₃ i p l₂, 
                begin 
                    simp,
                    have p₂ : length (reverse_core l₃ (h::l₂)) = length l₃ + length (h::l₂),
                    apply p, focus {simp [measure, inv_image], rw add_comm, apply nat.lt_succ_self },
                    rw p₂, simp
                end
                )
            ) 
            l₂
    
    @[simp] lemma l_rev {t : list α} : list.length (list.reverse t) = list.length t := by simp [reverse]

end list