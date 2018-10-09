namespace cat

universes u v
class category (obj : Type u) : Type (max u (v+1)) :=
(hom      : obj → obj → Type v)
(id       : Π X : obj, hom X X)
(comp     : Π {X Y Z : obj}, hom X Y → hom Y Z → hom X Z)
(id_comp : ∀ {X Y : obj} (f : hom X Y), comp (id X) f = f)
(comp_id : ∀ {X Y : obj} (f : hom X Y), comp f (id Y) = f)
(assoc   : ∀ {W X Y Z : obj} (f : hom W X) (g : hom X Y) (h : hom Y Z), comp (comp f g) h = comp f (comp g h))

attribute [simp] category.id_comp category.comp_id category.assoc

notation `𝟙` := category.id -- type as \b1
infixr ` ≫ `:80 := category.comp -- type as \gg
infixr ` ⟶ `:10 := category.hom -- type as \h

universes u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

section
structure functor (C : Type u₁) [category.{u₁ v₁} C] (D : Type u₂) [category.{u₂ v₂} D] : Type (max u₁ v₁ u₂ v₂) :=
(obj       : C → D)
(map      : Π {X Y : C}, (X ⟶ Y) → ((obj X) ⟶ (obj Y)))
(map_id   : ∀ (X : C), map (𝟙 X) = 𝟙 (obj X))
(map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = (map f) ≫ (map g))


infixr ` ⥤ `:70 := functor       -- type as \func --
instance {C : Type u₁} [category.{u₁ v₁} C] {D : Type u₂} [category.{u₂ v₂} D] : has_coe_to_fun (C ⥤ D) :=
{ F   := λ F, C → D,
  coe := λ F, F.obj }
end
lemma functor.ext 
  {C : Type u₁} [category.{u₁ v₁} C] {D : Type u₂} [category.{u₂ v₂} D] : 
  Π {F G : C ⥤ D} 
  (oe : F.obj = G.obj) 
  (me : ((eq.rec_on oe F.map) : Π {X Y : C}, (X ⟶ Y) → ((G.obj X) ⟶ (G.obj Y))) = G.map), F = G
  |⟨o,m,_,_⟩ ⟨_,_,_,_⟩ rfl rfl := rfl
namespace functor

section
variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
          {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
          {E : Type u₃} [ℰ : category.{u₃ v₃} E]
include 𝒞 𝒟 ℰ
/--
`F ⋙ G` is the composition of a functor `F` and a functor `G` (`F` first, then `G`).
-/
def comp 
    (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E :=
{ obj      := λ X, G (F X)
, map      := λ _ _ f, G.map (F.map f)
, map_id   := λ X, 
  calc G.map (F.map (𝟙 X)) = G.map (𝟙 (F.obj X)) : by simp [F.map_id]
                                         ... = 𝟙 (G.obj (F.obj X)) : by simp [G.map_id]
, map_comp := λ X Y Z f g, begin simp [functor.map_comp] end
}
infixr ` ⋙ `:80 := functor.comp
@[simp] lemma comp_map_expand {F : C ⥤ D} {G : D ⥤ E} {X Y : C} {f : X ⟶ Y}: (F ⋙ G).map f = G.map (F.map f)
:= begin refl end
end

def id (C : Type u₁) [𝒞 : category.{u₁ v₁} C] : C ⥤ C := 
{obj := λ X, X
, map := λ _ _ f, f
, map_id := λ X, rfl
, map_comp := λ X Y Z f g, rfl
}

lemma comp_id 
    {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
    {D : Type u₂} [𝒟 : category.{u₂ v₂} D] 
    : ∀ (F : C ⥤ D), (F ⋙ (functor.id D)) = F := 
    λ F, begin apply functor.ext _ _, reflexivity, reflexivity end

lemma id_comp
    {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
    {D : Type u₂} [𝒟 : category.{u₂ v₂} D] 
    : ∀ (F : C ⥤ D), ((functor.id C)⋙F) = F := 
    λ F, begin apply functor.ext _ _, reflexivity, reflexivity end

lemma assoc
    {C₁ : Type u₁} [𝒞₁ : category.{u₁ v₁} C₁] 
    {C₂ : Type u₂} [𝒞₂ : category.{u₂ v₂} C₂] 
    {C₃ : Type u₃} [𝒞₃ : category.{u₃ v₃} C₃] 
    {C₄ : Type u₄} [𝒞₄ : category.{u₄ v₄} C₄]
    : ∀ (F₁₂ : C₁ ⥤ C₂) (F₂₃ : C₂ ⥤ C₃) (F₃₄ : C₃ ⥤ C₄), F₁₂ ⋙ (F₂₃ ⋙ F₃₄) = (F₁₂ ⋙ F₂₃) ⋙ F₃₄  :=
    begin intros, apply functor.ext _ _, reflexivity, reflexivity end 

end functor
open functor

/-- The category of small categories -/
structure Cat : Type (max (u+1) (v+1)) :=
(ob : Type u) [cat : category.{u v} ob]
instance (𝒞 : Cat) : category (𝒞.ob) := 𝒞.cat
instance Cat_is_category : category.{(max (u+1) (v+1)) (max u v)} Cat :=
{ hom := λ 𝒞 𝒟, 𝒞.ob ⥤ 𝒟.ob
, id  := λ 𝒞, functor.id 𝒞.ob
, comp := λ 𝒞 𝒟 ℰ F G, F ⋙ G
, id_comp := λ 𝒞 𝒟 F, functor.id_comp _
, comp_id := λ 𝒞 𝒟 F, functor.comp_id _
, assoc := begin intros, apply functor.assoc end
}

structure nat_trans {C : Type u₁} {D : Type u₂} [category.{u₁ v₁} C] [category.{u₂ v₂} D] (F G : C ⥤ D) : Type (max u₁ v₂) :=
(app : Π X : C, (F.obj X) ⟶ (G.obj X))
(naturality : ∀ {X Y : C} (f : X ⟶ Y), (F.map f) ≫ (app Y) = (app X) ≫ (G.map f))
attribute [simp] nat_trans.naturality

infixr ` ⟹ `:50  := nat_trans             -- type as \==> or ⟹

namespace nat_trans
variables {C : Type u₁} {D : Type u₂} [𝒞 : category.{u₁ v₁} C] [𝒟 : category.{u₂ v₂} D]
variables {F G H : C ⥤ D}
include 𝒞 𝒟
instance : has_coe_to_fun (F ⟹ G) :=
{ F   := λ _, Π X:C, F X ⟶ G X, coe := λ τ, τ.app}

lemma ext : ∀ {τ σ : F ⟹ G} (p : τ.app = σ.app), τ = σ
|⟨a,_⟩ ⟨_,_⟩ rfl := rfl

def id : F ⟹ F :=
{app := λ X, category.id _
, naturality := λ X Y f, by simp
}

def vcomp (α : F ⟹ G) (β : G ⟹  H) : F ⟹ H :=
{app := λ X, α.app X ≫ β.app X
, naturality := begin intros, rw [<-category.assoc], rw [naturality], simp end
}

notation α `⊟` β:80 := vcomp α β


def hcomp 
  {E : Type u₃} [category.{u₃ v₃} E]
  {I J : D ⥤ E}
 (α : F ⟹ G) (β : I ⟹ J) : (F ⋙ I) ⟹ (G ⋙ J) :=
{app := λ X, I.map (α.app X) ≫ β.app (G.obj X)
, naturality := begin intros, simp, rw [<-category.assoc], rw [naturality], rw [category.assoc], rw [<-functor.map_comp], rw [naturality], rw [functor.map_comp] end
}




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