/- Y combinator -/


variables {α β : Type}
meta def Y : ((α → β) → α → β) → α → β | f x := f (Y f) x

universes u v

#eval to_string $ expr.subst ( (expr.var 1)) ```(nat.succ 0)

#eval to_string $ expr.is_internal_cnstr $ (expr.lam `hello binder_info.default (expr.var 1) $ expr.app (expr.app (expr.var 5) (expr.var 3)) `(4))

#eval to_string $ (expr.instantiate_var (expr.app (expr.var 5) (expr.var 2435)) `(1))
def e := Π a : Type u, Π b : Type v, a × b
#check e
#eval to_string $ expr.collect_univ_params $ expr.reflect e

#eval @undefined_core nat "wtf"


namespace hidden

definition cong (a b m : ℤ) : Prop := ∃ n : ℤ, b - a = m * n

notation a ` ≡ ` b ` mod ` m  := cong a b m 
set_option trace.simplify true
theorem cong_refl (m : ℤ) : ∀ a : ℤ, a ≡ a mod m :=
begin
intro a,
unfold cong,
existsi (0:ℤ),
simp
end

meta def trace_simp_lemmas : tactic unit :=
do
    l ← tactic.get_simp_lemmas_or_default none,
    str ← simp_lemmas.pp l,
    tactic.trace str

example : true := begin trace_simp_lemmas, trivial  end

end hidden


example (P : α → Prop) (Q : Prop) (h₁ : ∃ x, P(x)) (h₂ : ∀ x, P(x) → Q) : Q :=
begin
    cases h₁,
    apply h₂ _, assumption
end

