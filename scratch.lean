/- Y combinator -/


variables {α β : Type}
meta def Y {α : Type} : (α → α) → α | f := f (Y f)

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

namespace my_namespace
    constant X : Type u
    constants x y : X
    constant f : X → X
    constants  (P : X → Prop) (Q : Prop)
    /--Hello world-/
    axiom my_axiom : ∀ (a:X) (p : P(a)) (q:Q), Q
    #check my_axiom
    #check expr.mvar
    meta def scratch_tac : tactic unit := do
        -- a ← tactic.resolve_name `my_axiom >>= tactic.to_expr,
        -- l ← tactic.apply_core a {},
        -- g ← tactic.target,
        -- tactic.set_tag g [`hello.world],
        -- e ← tactic.head_eta_expand a,
        -- tactic.trace e,
        tactic.mk_fresh_name >>= tactic.trace,
        pure()

    example : Q :=
    begin
        scratch_tac,
        scratch_tac,
        scratch_tac,
        scratch_tac,
        tactic.rotate_left 1,
        sorry
    end
    example : true := begin 
        tactic.add_doc_string `nat "my dumb axiom is great at breaking maths yay.",
        tactic.doc_string `nat >>= tactic.trace,
        trivial 
    end
    #check nat
section scratch

end scratch
end my_namespace


end hidden


example (P : α → Prop) (Q : Prop) (h₁ : ∃ x, P(x)) (h₂ : ∀ x, P(x) → Q) : Q :=
begin
    cases h₁,
    apply h₂ _, assumption
end

example : ∀ (n : nat), n = n := 
begin
  intro,
  induction n,
end


namespace field_idea_auto_param
    -- eventually a sophisticated tactic that figures out if an elt is ≠ 0
    meta def nz_tactic := tactic.assumption 
    class dvr (R : Type u) extends (ring R) :=
    (inv(x:R) (p:x ≠ 0):  R)
    (inv_l : Π (x y : R) (p:y≠0), x * (inv y p)  = 1 )
    variables {R : Type u} [dvr R]
    def inv (y : R) (nz : y ≠ 0 . nz_tactic) : R := dvr.inv y nz

    def div (x y : R) (nz : y ≠ 0 . nz_tactic) : R := x * (inv y)
    infix ` /. `:50 := div

    variables {x y : R} 
    variable (xz : x ≠ 0 . nz_tactic) -- I was really hoping that this would be allowed

    example (x y : R) (xz : x ≠ 0) (yz : y ≠ 0) : (1 /. (x * y)) = (1 /. x) * (1 /. y) := sorry

end field_idea_auto_param

namespace field_idea_class
    class my_division_ring (R : Type u) extends (integral_domain R) :=
    (inv : Π(x:R) [x ≠ 0],  R)
    (inv_l (x : R) [nz:x ≠ 0] : x * (@inv x nz)  = 1 )
    (inv_r (x : R) [nz:x ≠ 0] : (@inv x nz) * x  = 1 )

    variables {R : Type u} [my_division_ring R]
    def inv (y : R) [nz:y ≠ 0] : R := @my_division_ring.inv _ _ y nz

    def div (x y : R) [y ≠ 0] : R := x * (inv y)
    infix ` ÷ `:50 := div

    variables {x y : R} [x ≠ 0] [y ≠ 0]
    def asdf : ((x * y) ≠ 0) := mul_ne_zero ‹x ≠ 0› ‹y ≠ 0›

    example : (1 ÷ (x * y)) = (1 ÷ x) * (1 ÷ y) := sorry
    -- calc (1 ÷ (x * y)) = inv(x * y) * 1 : by sorry
    --      ...           = inv(x * y) * (x * inv(x)) * (y * inv(y)) : by sorry
    --      ...           = (inv(x * y) * (x * y)) * (inv(x) * inv(y)) : by ac_refl
    --      ...           = 1 * (1 * inv(x)) * (1 * inv(y)) : by sorry
    --      ...           = (1 ÷ x) * (1 ÷ y) : by sorry

end field_idea_class