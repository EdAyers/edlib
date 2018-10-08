namespace cat

universes u v
class category (obj : Type u) : Type (max u (v+1)) :=
(hom      : obj → obj → Type v)
(id       : Π X : obj, hom X X)
(comp     : Π {X Y Z : obj}, hom X Y → hom Y Z → hom X Z)
(id_comp : ∀ {X Y : obj} (f : hom X Y), comp (id X) f = f)
(comp_id : ∀ {X Y : obj} (f : hom X Y), comp f (id Y) = f)
(assoc   : ∀ {W X Y Z : obj} (f : hom W X) (g : hom X Y) (h : hom Y Z), comp (comp f g) h = comp f (comp g h))

notation `𝟙` := category.id -- type as \b1
infixr ` ≫ `:80 := category.comp -- type as \gg
infixr ` ⟶ `:10 := category.hom -- type as \h

universes u₁ v₁ u₂ v₂ u₃ v₃

structure functor (C : Type u₁) [category.{u₁ v₁} C] (D : Type u₂) [category.{u₂ v₂} D] : Type (max u₁ v₁ u₂ v₂) :=
(obj       : C → D)
(map      : Π {X Y : C}, (X ⟶ Y) → ((obj X) ⟶ (obj Y)))
(map_id   : ∀ (X : C), map (𝟙 X) = 𝟙 (obj X))
(map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = (map f) ≫ (map g))

infixr ` ⥤ `:70 := functor       -- type as \func --
instance {C : Type u₁} {D : Type u₂} [category.{u₁ v₁} C] [category.{u₂ v₂} D] : has_coe_to_fun (C ⥤ D) :=
{ F   := λ F, C → D,
  coe := λ F, F.obj }
namespace functor

/--
`F ⋙ G` is the composition of a functor `F` and a functor `G` (`F` first, then `G`).
-/
def comp 
    {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
    {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
    {E : Type u₃} [ℰ : category.{u₃ v₃} E]
    (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E :=
{ obj      := λ X, G (F X)
, map      := λ _ _ f, G.map (F.map f)
, map_id   := λ X, 
  calc G.map (F.map (𝟙 X)) = G.map (𝟙 (F.obj X)) : by simp [F.map_id]
                                         ... = 𝟙 (G.obj (F.obj X)) : by simp [G.map_id]
, map_comp := λ X Y Z f g, begin simp [functor.map_comp] end
}

def id (C : Type u₁) [𝒞 : category.{u₁ v₁} C] : C ⥤ C := 
{obj := λ X, X
, map := λ _ _ f, f
, map_id := λ X, rfl
, map_comp := λ X Y Z f g, rfl
}
infixr ` ⋙ `:80 := functor.comp

lemma comp_id 
    {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
    {D : Type u₂} [𝒟 : category.{u₂ v₂} D] : ∀ (F : C ⥤ D), (F ⋙ (functor.id D)) = (F : C ⥤ D) := λ F, begin simp [comp, id], simp,  end

/- [TODO] 
- functor comp is associative and identity works 
-/
end functor
open functor

structure nat_trans {C : Type u₁} {D : Type u₂} [category.{u₁ v₁} C] [category.{u₂ v₂} D] (F G : C ⥤ D) : Type (max u₁ v₂) :=
(app : Π X : C, (F X) ⟶ (G X))
(naturality : ∀ {X Y : C} (f : X ⟶ Y), (F.map f) ≫ (app Y) = (app X) ≫ (G.map f))

infixr ` ⟹ `:50  := nat_trans             -- type as \==> or ⟹

namespace nat_trans
instance {C : Type u₁} {D : Type u₂} [category.{u₁ v₁} C] [category.{u₂ v₂} D] {F G : C ⥤ D} : has_coe_to_fun (F ⟹ G) :=
{ F   := λ _, Π X:C, F X ⟶ G X, coe := λ τ, τ.app}
/- [TODO] 
- [ ] whiskering
- [ ] vertical comp
- [ ] horizontal comp
- [ ] tedious composition lemmas
-/
end nat_trans

structure Adjunction {C : Type u₁} {D : Type u₂} [category.{u₁ v₁} C] [category.{u₂ v₂} D] 
  (L : C ⥤ D) (R : D ⥤ C) :=
  (unit       : functor.id C ⟹ (L ⋙ R))
  (counit     : (R ⋙ L) ⟹ functor.id D)
  (triangle_1 : ∀ X : D, (unit (R X)) ≫ (R.map (counit X)) = 𝟙 (R X))
  (triangle_2 : ∀ X : C, (L.map (unit X)) ≫ (counit (L X)) = 𝟙 (L X))


end cat