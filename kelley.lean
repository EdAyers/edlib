/- How would one axiomatise Kelley's set theory in Lean? Like this: -/
namespace kelley
noncomputable theory

/--The space of all classes. -/
constant C : Type
constant ε : C → C → Prop
instance : has_mem C C := ⟨ε⟩

axiom I : ∀ {x y : C}, (∀ z, z ∈ x ↔ z ∈ y) → x = y
def is_set (x : C) : Prop := ∃ y:C, x ∈ y

constant sep (P : C → Prop) : C
--instance : has_sep C C := ⟨sep⟩
axiom II {P : C → Prop} : ∀ {x:C}, (x ∈ sep P) ↔ (is_set(x) ∧ P(x))
notation `{` binders `| ` r:(scoped f, sep f) `}` := r
variables {x y z: C}
definition D2 (x y : C) : C := {z|z ∈ x ∧ z ∈ y}
instance : has_inter C := ⟨D2⟩
definition D3 (x y : C) : C := {z|z ∈ x ∨ z ∈ y}
instance : has_union C := ⟨D3⟩
theorem T4a : z ∈ x ∪ y ↔ (z ∈ x) ∨ (z ∈ y) := ⟨λ x, (II.1 x).2,λ y, or.cases_on y (λ h, II.2 ⟨⟨_,h⟩,or.inl h⟩) (λ h, II.2 ⟨⟨_,h⟩,or.inr h⟩)⟩
theorem T4b : z ∈ x ∩ y ↔ (z ∈ x) ∧ (z ∈ y) := ⟨λ h, (II.1 h).2,λ ⟨h₁,h₂⟩, II.2 ⟨⟨_,h₁⟩,⟨h₁, h₂⟩⟩⟩
theorem T5a : x ∪ x = x := I (λ z, ⟨λ h, or.cases_on (II.1 h).2 id id,λ h, II.2 ⟨⟨_,h⟩,or.inl h⟩⟩)
theorem T5b : x ∩ x = x := I (λ z, ⟨λ h, and.cases_on (II.1 h).2 (λ _ h, h),λ h, II.2 ⟨⟨_,h⟩,⟨h,h⟩⟩⟩)
theorem T6a : x ∪ y = y ∪ x := sorry
theorem T6b : x ∩ y = y ∩ x := sorry
theorem T7a : (x ∪ y) ∪ z = x ∪ (y ∪ z) := sorry
theorem T7b : (x ∩ y) ∩ z = x ∩ (y ∩ z) := I $ λ a, 
    ⟨λ h, let ⟨h₂,h₃⟩ := T4b.1 h in let ⟨h₂,h₄⟩ := T4b.1 h₂ in T4b.2 ⟨h₂,T4b.2 ⟨h₄,h₃⟩⟩
    ,λ h, let ⟨h₂,h₃⟩ := T4b.1 h in let ⟨h₃,h₄⟩ := T4b.1 h₃ in T4b.2 ⟨T4b.2 ⟨h₂,h₃⟩, h₄⟩
    ⟩
theorem T8a : x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z) := sorry
theorem T8b : x ∪ (y ∩ z) = (x ∪ y) ∩ (x ∪ z) := sorry
definition D10 (x:C) : C := {y|y ∉ x}
prefix `~` := D10
theorem T11 : (~ (~ x)) = x := I $ assume z:C, 
    ⟨   assume h : z ∈ ~ (~ x),
        have h₂ : z ∉ ~x := (II.1 h).2, 
        classical.by_contradiction (
            assume h₃ : z ∉ x, 
            have h₄ : z ∈ { z | z ∉ x}, from II.2 $ ⟨⟨_,h⟩,h₃⟩,
            show false, from h₂ h₄
            )
    , λ h, II.2 $ ⟨⟨_,h⟩,λ h₂, absurd h (II.1 h₂).2⟩
    ⟩

definition D13 (x y : C) := x ∩ (~ y)
instance : has_sub C := ⟨D13⟩
theorem T14 : x ∩ (y - z) = (x ∩ y) - z := eq.symm T7b
definition D15 :C := {x|false}
instance : has_emptyc C := ⟨D15⟩
theorem T16 : x ∉ (∅:C) := λ h, (II.1 h).2
theorem T17a : ∅ ∪ x = x := sorry
theorem T17b : ∅ ∩ x = ∅ := sorry
definition U : C := {x|true}
theorem T19 : x ∈ U ↔ is_set x := ⟨λ h, (II.1 h).1, λ h, II.2 ⟨h,⟨⟩⟩⟩
theorem T20a : x ∪ U = U := sorry
theorem T20b : x ∩ U = x := sorry
theorem T21a : (~ ∅) = U := I $ λ z, ⟨λ h, let ⟨s,h⟩ := II.1 h in II.2 ⟨s,⟨⟩⟩,λ h, let ⟨s,h⟩ := II.1 h in II.2 ⟨s,T16⟩⟩
theorem T21b : (~ U) = ∅ := calc (~ U) = ~ ~ ∅ : by rw <- T21a ... = ∅ : T11
definition D22 (x : C) := {z|∀ y, y ∈ x → z ∈ y}
prefix `⋂`:100 := D22
definition D23 (x : C) := {z|∃ y, y ∈ x ∧ z ∈ y}
prefix `⋃`:100 := D23

theorem T24a : ⋂ ∅ = U := I $ λ z, 
⟨assume h: z ∈ ⋂∅, II.2 ⟨⟨_,h⟩,⟨⟩⟩
,assume h: z ∈ U, II.2 ⟨T19.1 h,λ y h₂, false.rec_on _ (T16 h₂)⟩
⟩
theorem T24b : ⋃ ∅ = ∅ := I $ λ z, ⟨λ h, let ⟨_,_,h₂,_⟩ := II.1 h in false.rec_on _ (T16 h₂),λ h, false.rec_on _ (T16 h)⟩ 
definition D25 (x y : C) : Prop := ∀ z, z ∈ x → z ∈ y
instance : has_subset C := ⟨D25⟩
-- etc etc
theorem T26a : ∅ ⊆ x := λ z ze, false.rec_on _ (T16 ze)
theorem T26b : x ⊆ U := λ z ze, II.2 ⟨⟨_,ze⟩, ⟨⟩⟩
theorem T27 : x ⊆ y → y ⊆ x → x = y := λ xy yx, I $ λ z, ⟨xy _,yx _⟩
theorem T28 : x ⊆ y → y ⊆ z → x ⊆ z := λ xy yz a ax, yz _ $ xy _ ax
theorem T29 : x ⊆ y ↔ x ∪ y = y := sorry
theorem T30 : x ⊆ y ↔ x ∩ y = x := sorry
theorem T31a : x ⊆ y → ⋃x ⊆ ⋃y := sorry
theorem T31b : x ⊆ y → ⋂y ⊆ ⋂x := sorry
theorem T32 : x ∈ y → x ⊆ ⋃ y := sorry
theorem T32b : x ∈ y → ⋂ y ⊆ x := sorry
-- the powerset axiom
axiom III : is_set(x) → ∃ y, is_set(y) ∧ ∀ z, z ⊆ x → z ∈ y
theorem T33 : is_set(x) → (z ⊆ x) → is_set(z) := λ h₁ h₂,
    let ⟨w,h₃,h₄⟩ := III (h₁) in ⟨w,h₄ _ h₂⟩
theorem T34a : ∅ = ⋂ U := sorry
theorem T34b : U = ⋃ U := sorry
theorem T35 : x ≠ ∅ → is_set ⋂x := sorry
definition D36 (x:C) : C := {y|y⊆x}
prefix `P`:100 := D36
lemma x_in_P_x : is_set(x) → x ∈ P x := λ sx, II.2 ⟨sx,λ z h, h⟩
theorem T37 : U = P U := I $ λ x, ⟨λ h, II.2 $ ⟨⟨_,h⟩,λ y h₂, II.2 $ ⟨⟨_,h₂⟩,⟨⟩⟩⟩,λ p, II.2 ⟨(II.1 p).1,⟨⟩⟩⟩
theorem T38a : is_set x → is_set (P x) :=
    assume h₁, 
    let ⟨y,h₂,h₃⟩ := III h₁ in
    have P x ⊆ y, from λ z h₄, h₃ _ (II.1 h₄).2, 
    T33 h₂ this

definition R := {y|y∉y}
lemma R_not_in_R : R ∉ R := assume h : R ∈ R, absurd h (II.1 h).2
lemma R_not_set : ¬ is_set(R) := λ c, R_not_in_R $ II.2 $ ⟨c,R_not_in_R⟩
lemma R_sub_U : R ⊆ U := λ z h, II.2 ⟨⟨_,h⟩,⟨⟩⟩
theorem T39 : ¬ is_set(U) := λ h, absurd (T33 h R_sub_U) R_not_set
definition singleton (x:C) := {z|x ∈ U → z = x}
definition insert (x X : C) := (singleton x) ∪ X
notation `⟮` l:(foldr `, ` (h t, insert h t) ∅ `⟯`) := l
theorem T41 : is_set(x) → ∀ {y}, y ∈ ⟮x⟯ ↔ y = x := sorry
theorem T41b : is_set(x) → x ∈ ⟮x⟯ := sorry
theorem T42 : (is_set(x)) → (is_set ⟮x⟯) := sorry
theorem T43 : ⟮x⟯ = U ↔ ¬is_set x := sorry
theorem T44a : is_set x → ⋂⟮x⟯ = x := sorry
theorem T44b : is_set x → ⋃⟮x⟯ = x := sorry
theorem T44c : ¬is_set x → ⋂⟮x⟯ = ∅ := sorry
theorem T44d : ¬is_set x → ⋃⟮x⟯ = U := sorry
axiom IV: is_set(x) → is_set(y) → is_set (x ∪ y) 

theorem T46a : is_set x → is_set y → is_set (⟮x,y⟯) := sorry
theorem T46b : is_set x → is_set y → ((z ∈ ⟮x,y⟯) ↔ (z = x ∨ z = y)) := sorry
theorem T46c : (⟮x,y⟯ = U) ↔ ((¬ is_set x) ∨ (¬ is_set y)) := sorry
theorem T46d : x ∈ z → y ∈ z → ⟮x,y⟯ ⊆ z := λ xz yz u up,
    have h : (u = x ∨ u = y), from (T46b ⟨z,xz⟩ ⟨z,yz⟩).1 up,
    or.rec_on h (λ h, eq.symm h ▸ xz) (λ h, eq.symm h ▸ yz)
theorem T46e : is_set x → is_set y → ⟮x,y⟯ ≠ ∅ := sorry
theorem T46f : is_set x → is_set y →  x ∈ ⟮x,y⟯ := sorry
theorem T46g : is_set x → is_set y →  y ∈ ⟮x,y⟯ := sorry
theorem T47a : is_set x → is_set y → ⋂ ⟮x,y⟯ = x ∩ y := sorry
theorem T47b : is_set x → is_set y → ⋃ ⟮x,y⟯ = x ∪ y := sorry
theorem T47c : (¬is_set x ∨ ¬is_set y) → ⋂ ⟮x,y⟯ = ∅ := sorry
theorem T47d : (¬is_set x ∨ ¬is_set y) → ⋃ ⟮x,y⟯ = U := sorry
/-- Ordered Pair -/
definition D48 (x y : C) := ⟮⟮x⟯,⟮x,y⟯⟯
notation `[`x`,`y`]` := D48 x y
theorem T49a : is_set x → is_set y → is_set [x,y] := λ sx sy, T46a (T42 sx) (T46a sx sy)
theorem T49b : is_set [x,y] → is_set x := sorry
theorem T49c : is_set [x,y] → is_set y := sorry
theorem T49d : ¬is_set [x,y] → [x,y] = U := sorry
theorem T50 : is_set x → is_set y →
      ⋃[x,y] = ⟮x,y⟯
    ∧ ⋂[x,y] = ⟮x⟯
    ∧ ⋃⋂[x,y] = x
    ∧ ⋂⋂[x,y] = x
    ∧ ⋃⋃[x,y] = x ∪ y
    ∧ ⋂⋃[x,y] = x ∩ y
:= sorry
definition fst (x:C) := ⋂ ⋂ x -- D51
definition snd (x:C) := (⋂⋃x) ∪ (⋃⋃x - ⋃⋂x) -- D52
theorem T53 : snd U = U := sorry
theorem T54a : (is_set x) → (is_set y) → ((fst [x,y]) = x) ∧ (snd [x,y] = y) := sorry
theorem T54b : ¬(is_set x ∧ is_set y) → ((fst [x,y]) = U) ∧ (snd [x,y] = U) := sorry
theorem T55 {x y u v : C} : [x,y] = [u,v] → x = u ∧ y = v := sorry
definition is_relation (r:C) : Prop := ∀ z, z ∈ r → ∃ x y, z = [x,y]
definition D57 (r s : C) := {u| ∃ x y z, u = [x,z] ∧ [x,y] ∈ s ∧ [y,z] ∈ r}
infix ` ∙ `:80 := D57
variables {r s t : C} 
theorem T58 : (r ∙ s) ∙ t = r ∙ (s ∙ t) := sorry
theorem T59a : r ∙ (s ∪ t) = (r ∙ s) ∪ (r ∙ t) := 
    I $ λ p, 
    ⟨λ h, let ⟨h₁,x,y,z,h₂,h₃,h₄⟩ := II.1 h in let ⟨h₅,h₆⟩ := II.1 h₃ in II.2 ⟨h₁, or.cases_on h₆ (λ h₇, or.inl $ II.2 ⟨h₁,x,y,z,h₂,h₇,h₄⟩) (λ h₇, or.inr $ II.2 ⟨h₁,x,y,z,h₂,h₇,h₄⟩)⟩
    ,λ h, let ⟨h₁,h₂⟩ := II.1 h in or.cases_on h₂ (λ h₃,let ⟨h₃,x,y,z,h₄,h₅,h₆⟩ := II.1 h₃ in II.2 ⟨h₃,x,y,z,h₄,T4a.2 $ or.inl h₅,h₆⟩) (λ h₃,let ⟨h₃,x,y,z,h₄,h₅,h₆⟩ := II.1 h₃ in II.2 ⟨h₃,x,y,z,h₄,T4a.2 $ or.inr h₅,h₆⟩) 
    ⟩
theorem T59b : r ∙ (s ∩ t) ⊆ (r ∙ s) ∩ (r ∙ t) := λ a h₁,
  let ⟨h₂,x,y,z,h₃,h₄,h₅⟩ := (II.1 h₁) in
  let ⟨h₆,h₇,h₈⟩ := II.1 h₄ in
  II.2 ⟨h₂, II.2 ⟨h₂,x,y,z,h₃,h₇,h₅⟩, II.2 ⟨h₂,x,y,z,h₃,h₈,h₅⟩⟩
definition inverse (r:C) : C := {s|∃ x y, s = [x,y] ∧ [y,x] ∈ r}
postfix `⁻¹` := inverse
theorem T61 : r ⁻¹ ⁻¹ = r := sorry
theorem T62 : (r ∙ s) ⁻¹ = s ⁻¹ ∙ r ⁻¹ := sorry
definition is_function (f : C) := is_relation f ∧ ∀ x y z, [x,y] ∈ f → [x,z] ∈ f → y = z
definition domain (f:C) := {x|∃ y, [x,y] ∈ f}
definition range (f:C) := {y|∃ x, [x,y] ∈ f}

variables {f g : C}
theorem T64 : is_function f → is_function g → is_function (f ∙ g) := sorry
theorem T67a : domain U = U := sorry
theorem T67b : range U =  U := sorry
definition apply (f : C) (x : C) := ⋂ {y|[x,y] ∈ f}
instance function_coe : has_coe_to_fun C := ⟨λ x,C→C,apply⟩
theorem T69a : x ∉ (domain f) → f(x) = U := sorry
theorem T69b : x ∈ (domain f) → f(x) ∈ U := sorry
theorem T71 : is_function f → is_function g → (∀ x, f(x) = g(x)) → f = g := sorry
-- Axiom of substitution.
axiom V: ∀ {f : C}, is_function f → is_set (domain f) → is_set(range f)
axiom VI: is_set(x) → is_set(⋃ x)

definition D72 (x y : C) := {p|∃ u v, p = [u,v] ∧ u∈x ∧ v∈y}
infix ` ⨉ `:100 := D72
lemma prod_is_rel : is_relation (x ⨉ y) := λ z zr, let ⟨h₁,u,v,zuv,ux,vy⟩ := II.1 zr in ⟨u,v,zuv⟩
theorem T73 : (is_set x) → (is_set y) → is_set (⟮x⟯ ⨉ y) := sorry
theorem T74 : is_set x → is_set y → is_set (x ⨉ y) := sorry
definition D76 (x y : C) : C := {f|is_function f ∧ domain f = x ∧ range f ⊆ y}
infix ` => `:90 := D76
lemma function_sub_PPproduct : (x => y) ⊆ P (x ⨉ y) := 
λ f h, let ⟨h₁,⟨h₂,h₃⟩,h₄,h₅⟩ := II.1 h in II.2 ⟨h₁,λ p h₆, II.2 ⟨⟨_,h₆⟩, let ⟨u,v,h₇⟩ := h₂ _ h₆ in ⟨u,v,h₇,have u ∈ domain f, from II.2 sorry, h₄ ▸ this,sorry⟩⟩⟩
theorem T77 : is_set x → is_set y → is_set (x => y) := λ h₁ h₂, sorry

notation x` -`r`> `y := [x,y] ∈ r

definition connects (r x : C) := ∀ (u v ∈ x), (u -r> v) ∨ (v -r> u) ∨ (u = v)
definition transitive (r x : C) := ∀ (u v w ∈ x), (u -r> v) → (v -r> w) → (u -r> w)
definition asymmetric (r x : C) := ∀ (u v ∈ x), (u -r> v) → ¬(v -r> u)
definition first_mem (z r x : C) := z ∈ x ∧ ∀ y ∈ x, ¬ (y-r>z)  
/-- r well-orders x -/
definition well_orders (r x : C) := connects r x ∧ ∀ y, y ⊆ x → y ≠ ∅ → ∃ z, first_mem z r y
instance : has_coe (x ∈ y) (is_set x) := ⟨λ xy, ⟨y,xy⟩⟩
theorem T88a : well_orders r x → asymmetric r x := 
    λ ⟨hc,fm⟩ u v,
    assume ux : u ∈ x,
    assume vx : v ∈ x,
    assume uv : u -r> v,
    assume vu : v -r> u,
    have h₁ : ⟮u,v⟯ ⊆ x, from T46d ux vx,
    let ⟨z,h₂,h₃⟩ := fm _ h₁ (T46e ux vx) in
    or.rec_on ((T46b ⟨x,ux⟩ ⟨x,vx⟩).1 h₂) 
      (assume h : z = u, h₃ v (T46g ux vx) (eq.symm h ▸ vu)) 
      (assume h : z = v, h₃ u (T46f ux vx) (eq.symm h ▸ uv))
theorem T88b : well_orders r x → transitive r x := 
λ ⟨hc, fm⟩ u v w ux vx wx uv vw, classical.by_contradiction (λ nuw, 
    or.rec_on (hc w u wx ux) (λ h, 
        let t := ⟮u,v,w⟯ in
        have tsx : t ⊆ x, from (λ a ha, sorry),
        have tne : t ≠ ∅, from sorry,
        let ⟨z,h₁,h₂⟩ := fm _ tsx tne in
        sorry -- [TODO] rec on u,v,w again ☹
    ) (λ h, or.rec_on h (λ uw, absurd uw nuw) (λ uw, T88a ⟨hc,fm⟩ u v ux vx uv (uw ▸ vw))) 
)
/-- y is an r-section on x-/
definition sect (y r x : C) := y ⊆ x ∧ well_orders r x ∧ ∀ (u ∈ x) (v ∈ y), (u -r> v) → u ∈ y
theorem T90 : x ≠ ∅ → (∀ y ∈ x, sect y r x) → sect (⋃x) r x ∧ sect (⋂x) r x := sorry
theorem T91 : sect y r x → y ≠ x → ∃ v∈x, y = {u|u∈x ∧ u-r>v} := sorry
theorem T92 : sect x r z → sect y r z → x ⊆ y ∨ y ⊆ x := sorry
/--f is r-s-order preserving. -/
definition order_pres (f r s : C) := 
      is_function f 
    ∧ well_orders r (domain f)
    ∧ well_orders s (range f) 
    ∧ ∀ u v : C, 
        u ∈ (domain f) 
        → v ∈ (domain f) 
        → (u-r>v) 
        → (f(u) -s> f(v)) 
theorem T94 : sect x r y → order_pres f r r → domain f = x → range f = y → ∀ u ∈ x, ¬f(u) -r> u := sorry
definition isomorphism (f:C) := is_function f ∧ is_function f⁻¹
theorem T96 : order_pres f r s → isomorphism(f) ∧ order_pres (f⁻¹) s r := sorry
theorem T97 : 
       order_pres f r s 
    → order_pres g r s 
    → sect (domain f) r x 
    → sect (domain g) r x 
    → sect (range f) s y
    → sect (range g) s y
    → f ⊆ g ∨ g ⊆ f
    := sorry
definition order_pres_in (f r s x y : C) :=
      well_orders r x
    ∧ well_orders s y
    ∧ order_pres f r s
    ∧ sect (domain f) r x
    ∧ sect (range f) s y
theorem T99 : well_orders r x → well_orders s y → ∃ f, order_pres_in f r s x y ∧ (domain f = x ∨ range f = y) := sorry
theorem T100 : 
       well_orders r x 
    → well_orders s y 
    → is_set x 
    → ¬is_set y 
    → ∃! f, order_pres_in f r s x y ∧ domain f = x
    := sorry
/-- Regularity -/
axiom VII: x ≠ ∅ → ∃ y, y ∈ x ∧ x ∩ y = ∅

theorem T101 : x ∉ x := 
    assume h₁ : x ∈ x,
    have sx : is_set x, from h₁,
    have h₂ : x ≠ ∅, from assume o : x = ∅, absurd h₁ (eq.symm o ▸ T16),
    have h₃ : x ∈ ⟮x⟯, from T41b h₁,
    have h₄ : ⟮x⟯ ≠ ∅, from
        assume h₅ : ⟮x⟯ = ∅,
        have h₆ : x ∈ (∅:C), from h₅ ▸ h₃,
        absurd h₆ T16,
    have r :  ∃ (y : C), y ∈ ⟮x⟯ ∧ ⟮x⟯ ∩ y = ∅, from @VII ⟮x⟯ h₄,
    let ⟨y,r⟩ := r in
    have h₅ : y ∈ ⟮x⟯, from r.1,
    have h₆ : ⟮x⟯ ∩ y = ∅, from r.2,
    have h₇ : y = x, from (T41 sx).1 h₅,
    have h₈ : y ∈ y, from eq.symm h₇ ▸ h₁,
    have h₉ : y ∈ ⟮x⟯ ∩ y, from T4b.2 ⟨h₅, h₈⟩,
    have h₁₀ : y ∈ (∅:C), from h₆ ▸ h₉,
    absurd h₁₀ T16

theorem T102 : x ∈ y → y ∈ x → false := λ xy yx,
    let z := ⟮x,y⟯ in
    have sx : is_set x, from xy,
    have sy : is_set y, from yx,
    have h₁ : z ≠ ∅, from T46e sx sy,
    let ⟨q,h₂,h₃⟩ := VII h₁ in
    sorry -- same proof structure as T101.

definition E : C := {p|∃ x y,p=[x,y] ∧ x ∈ y}
theorem T104 : ¬is_set(E) := sorry
definition is_full (x:C) := ∀ y ∈ x, y ⊆ x
definition is_ordinal (x:C) := connects E x ∧ is_full x
theorem T107 : is_ordinal x → well_orders E x := sorry

theorem T108 : is_ordinal x → y ⊆ x → y ≠ x → is_full y → y ∈ x := sorry
theorem T109 : is_ordinal x → is_ordinal y → x ⊆ y ∨ y ⊆ x := sorry
theorem T110 : is_ordinal x → is_ordinal y → x ∈ y ∨ y ∈ x ∨ x = y := sorry
theorem T111 : is_ordinal x → y ∈ x → is_ordinal y := sorry
definition R : C := {x|is_ordinal x}
theorem T113a : is_ordinal R := sorry
theorem T113b : ¬is_set R := sorry
theorem T114 : sect E R x → is_ordinal x := sorry
definition is_ordinal_number (x:C) := x ∈ R
definition lt (x y : C) := x ∈ y
instance :has_lt C := ⟨lt⟩
definition le (x y : C) := x ∈ y ∨ x = y
instance : has_le C := ⟨le⟩
theorem T118 : is_ordinal x → is_ordinal y → x ≤ y ↔ x ⊆ y := sorry
theorem T119 : is_ordinal x → x = {y|y ∈ R ∧ y < x} := sorry
theorem T120 : x ⊆ R →is_ordinal  ⋃x := sorry
theorem T121 : x ⊆ R → x ≠ ∅ → ⋂x ∈ x := sorry
definition succ (x : C) := x ∪ ⟮x⟯
theorem T123 : x ∈ R → first_mem (succ x) E {y|y∈R ∧ x < y} := sorry
theorem T124 : x ∈ R → ⋃(succ x) = x := sorry
definition D125 (f x : C) := f ∩ (x ⨉ U)
notation f`↓`x := D125 f x
theorem T126 : is_function y → 
    (is_function (y↓x)) 
    ∧ ((domain y↓x) = x ∩ (domain y)) 
    ∧ (∀ (z ∈ (domain (y↓x))), (y↓x) z = y z) 
:= sorry

/-- Infinity -/
axiom VIII: ∃ y, is_set(y) ∧ ∅ ∈ y ∧ ∀ x, x ∈ y → x ∪ ⟮x⟯ ∈ y
lemma empty_is_set : is_set(∅) := let ⟨y,_,ey,_⟩ := VIII in ⟨y,ey⟩
/-- Choice -/
axiom IX: ∃ c, is_function(c) ∧ domain(c) = U - ⟮∅⟯



end kelley