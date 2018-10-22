import .set .list
namespace cat

universes u v

class has_hom (obj : Type u) : Type (max u (v + 1)) :=
(hom : obj → obj → Type v)
infixr ` ⟶ `:10 := has_hom.hom -- type as \h
@[inline] def hom (obj : Type u) [has_hom obj] (X : obj) (Y : obj) := @has_hom.hom obj _ X Y

class has_id_comp (obj : Type u) extends has_hom obj := 
(id : Π {X : obj}, X ⟶ X)
(comp : Π {X Y Z : obj}, (X ⟶ Y) → (Y⟶ Z) → (X ⟶Z))
@[inline] def comp (obj : Type u) [has_id_comp obj] {X Y Z : obj} := @has_id_comp.comp obj _ X Y Z
@[reducible] def has_id_comp_id {obj : Type u} [has_id_comp obj] {X : obj} : X ⟶ X := has_id_comp.id obj
@[reducible] def has_id_comp_id_exp {obj : Type u} [has_id_comp obj] (X : obj) : X ⟶ X := has_id_comp.id obj
notation `𝟙` := has_id_comp_id -- type as \b1
notation `𝟙_`X := has_id_comp_id_exp X -- type as \b1
infixr ` ≫ `:80 := has_id_comp.comp -- type as \gg

class category (obj : Type u) extends has_id_comp obj :=
-- (hom      : obj → obj → Type v)
-- (id       : Π X : obj, hom X X)
-- (comp     : Π {X Y Z : obj}, hom X Y → hom Y Z → hom X Z)
(id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 ≫ f = f)
(comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 = f)
(assoc   : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ (g ≫ h))

attribute [simp] category.id_comp category.comp_id category.assoc

universes u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

section iso_epi_mono
  variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {X Y Z : C}
  include 𝒞
  def is_epic (f : X ⟶ Y) := ∀ (g₁ g₂ : Y ⟶ Z), f ≫ g₁ = f ≫ g₂ → g₁ = g₂
  def is_monic (f : Y ⟶ Z) := ∀ (g₁ g₂ : X ⟶ Y), g₁ ≫ f =  g₂ ≫ f → g₁ = g₂
  -- idea: make constructive?
  def is_iso (f : X ⟶ Y) := ∃ (g : Y ⟶ X), f ≫ g = 𝟙 ∧ g ≫ f = 𝟙
  structure iso (X Y : C) := 
  (f : X ⟶ Y)
  (g : Y ⟶ X)
  (fg_id : f ≫ g = 𝟙)
  (gf_id : g ≫ f = 𝟙)
  infixr ` ⟷ ` :10 := iso 
  instance : has_coe (@iso C 𝒞 X Y) (X ⟶ Y) := ⟨λ x, x.f⟩
end iso_epi_mono

section
structure functor (C : Type u₁) [category.{u₁ v₁} C] (D : Type u₂) [category.{u₂ v₂} D] : Type (max u₁ v₁ u₂ v₂) :=
(obj       : C → D)
(map      : Π {X Y : C}, (X ⟶ Y) → ((obj X) ⟶ (obj Y)))
(map_id   : ∀ (X : C), map (𝟙 : X ⟶ X) = 𝟙)
(map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = (map f) ≫ (map g))
attribute [simp] functor.map_id functor.map_comp


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
    include 𝒞 𝒟 

    --@[simp] lemma functor_map_id {F : C ⥤ D} {X : C} : F.map (𝟙 X) = 𝟙 (F.obj X) := F.map_id _

    variables {E : Type u₃} [ℰ : category.{u₃ v₃} E]
    include ℰ
    /--
    `F ⋙ G` is the composition of a functor `F` and a functor `G` (`F` first, then `G`).
    -/
    def comp 
        (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E :=
    { obj      := λ X, G (F X)
    , map      := λ _ _ f, G.map (F.map f)
    , map_id   := λ X, 
      calc G.map (F.map (𝟙 : X ⟶ X)) = G.map (𝟙) : by rw [F.map_id]
                                  ... = 𝟙 : by rw [G.map_id]
    , map_comp := λ X Y Z f g, begin simp [functor.map_comp] end
    }
    infixr ` ⋙ `:80 := functor.comp
    @[simp] lemma comp_obj_expand {F : C ⥤ D} {G : D ⥤ E} {X : C} : (F ⋙ G).obj X = G.obj (F.obj X) := rfl
    @[simp] lemma comp_map_expand {F : C ⥤ D} {G : D ⥤ E} {X Y : C} {f : X ⟶ Y}: (F ⋙ G).map f = G.map (F.map f)
    := begin refl end
  end

  def id (C : Type u₁) [𝒞 : category.{u₁ v₁} C] : C ⥤ C := 
  { obj := λ X, X
  , map := λ _ _ f, f
  , map_id := λ X, rfl
  , map_comp := λ X Y Z f g, rfl
  }
  @[simp] lemma  id_obj_expand (C : Type u₁) [𝒞 : category.{u₁ v₁} C] {X : C} : (functor.id C).obj X = X := rfl 
  @[simp] lemma  id_map_expand (C : Type u₁) [𝒞 : category.{u₁ v₁} C] {X Y : C} {f : X ⟶ Y} : (functor.id C).map f = f := rfl 

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

structure nat_trans 
  {C : Type u₁} {D : Type u₂} [category.{u₁ v₁} C] [category.{u₂ v₂} D] 
  (F G : C ⥤ D) : Type (max u₁ v₂) :=
(app : Π X : C, (F.obj X) ⟶ (G.obj X))
(naturality : ∀ {X Y : C} (f : X ⟶ Y), (F.map f) ≫ (app Y) = (app X) ≫ (G.map f))
attribute [simp] nat_trans.naturality

infixr ` ⟹ `:50  := nat_trans             -- type as \==> or ⟹

namespace nat_trans
  variables {C : Type u₁} {D : Type u₂} [𝒞 : category.{u₁ v₁} C] [𝒟 : category.{u₂ v₂} D]
  variables {F G H I : C ⥤ D}
  include 𝒞 𝒟
  instance : has_coe_to_fun (F ⟹ G) :=
  { F   := λ _, Π X:C, F X ⟶ G X, coe := λ τ, τ.app}

  lemma ext : ∀ {τ σ : F ⟹ G} (p : τ.app = σ.app), τ = σ
  |⟨a,_⟩ ⟨_,_⟩ rfl := rfl

  def id : F ⟹ F :=
  { app := λ X, 𝟙_(F.obj X)
  , naturality := λ X Y f, by simp
  }
  @[simp] lemma reduce_id {X : C} : nat_trans.id.app X = 𝟙_(F.obj X) := rfl

  def vcomp (α : F ⟹ G) (β : G ⟹  H) : F ⟹ H :=
  {app := λ X, α.app X ≫ β.app X
  , naturality := begin intros, rw [<-category.assoc], rw [naturality], simp end
  }

  notation α ` ⊟ ` β:80 := vcomp α β -- I usually just use ≫

  instance Hom_is_category : category.{(max u₁ v₁ u₂ v₂) (max u₁ v₂)} (C ⥤ D) :=
  { hom := λ F G, F ⟹ G
  , id := λ F, nat_trans.id
  , comp := λ F G H α β, vcomp α β
  , id_comp := begin intros, apply ext, simp[vcomp, id]end
  , comp_id := begin intros, apply ext, simp[vcomp, id]end
  , assoc := begin intros, apply ext, simp [vcomp] end
  }

  @[simp] lemma vcomp_reduce {α : F ⟹ G} {β : G ⟹ H} : (α ⊟ β).app = λ X, (α.app X)≫ (β.app X) := rfl
  @[simp] lemma nat_trans_comp_reduce {α : F ⟶ G} {β : G ⟶ H} : (α ≫ β).app = λ X, (α.app X)≫ (β.app X) := rfl
  @[simp] lemma nat_trans_id_reduce : (𝟙 : F ⟶ F).app = λ X, 𝟙 := rfl

  def hcomp 
    {E : Type u₃} [category.{u₃ v₃} E]
    {I J : D ⥤ E}
    (α : F ⟹ G) (β : I ⟹ J) : (F ⋙ I) ⟹ (G ⋙ J) :=
  { app := λ X, I.map (α.app X) ≫ β.app (G.obj X)
  , naturality := begin intros, simp, rw [<-category.assoc], rw [naturality], rw [category.assoc], rw [<-functor.map_comp], rw [naturality], rw [functor.map_comp] end
  }

  notation α `◫` β : 80 := hcomp α β

  /- [TODO] 
  - [ ] whiskering
  - [ ] hcomp makes Cat a 2-category. 
  -/
end nat_trans
open nat_trans

section product
  variables {C : Type u₁} {D : Type u₂} [𝒞 : category.{u₁ v₁} C] [𝒟 : category.{u₂ v₂} D]
  include 𝒞 𝒟
  instance product_is_cat 
    : category.{(max u₁ u₂) (max v₁ v₂)} (C × D) := 
  { hom := λ x y, (x.1 ⟶ y.1) × (x.2 ⟶ y.2)
  , id  := λ p, ⟨𝟙, 𝟙⟩
  , comp := λ x y z f g, ⟨f.1 ≫ g.1, f.2 ≫ g.2⟩
  , id_comp := begin intros, simp end
  , comp_id := begin intros, simp end
  , assoc := begin intros, simp end
  }
  attribute [reducible] cat.product_is_cat
  variables {X : C × D}
  --@[simp] lemma product_id_fst : (𝟙_X).1 = 𝟙_(X.1) := 
  @[simp] lemma product_id : (𝟙_X) = (𝟙_X.fst, 𝟙_X.snd) := rfl
  @[simp] lemma product_comp_fst
  {X Y Z: C × D} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).fst = f.fst ≫ g.fst := rfl
  @[simp] lemma product_comp_snd
  {X Y Z: C × D} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).snd = f.snd ≫ g.snd := rfl
  attribute [simp] cat.product_is_cat
  def fst_functor : (C × D) ⥤ C :=
  {obj := λ P, P.1, map := λ P Q f, f.1, map_id := λ P, rfl, map_comp := λ P Q R f g , rfl}
end product 
section product_coe
    variables {C₁ : Type u₁} [𝒞₁ : category.{u₁ v₁} C₁] 
              {C₂ : Type u₂} [𝒞₂ : category.{u₂ v₂} C₂] 
              {C₃ : Type u₃} [𝒞₃ : category.{u₃ v₃} C₃] 
              {C₄ : Type u₄} [𝒞₄ : category.{u₄ v₄} C₄]
  include 𝒞₁ 𝒞₂ 𝒞₃ 𝒞₄
  def prod_functor_of_functor_prod : ((C₁ ⥤ C₂) × (C₃ ⥤ C₄)) → ((C₁ × C₃) ⥤ (C₂ × C₄)) :=λ F, {
     obj := λ p, (F.1.obj p.1, F.2.obj p.2)
    , map := λ P Q p, (F.1.map p.1,F.2.map p.2)
    , map_id := λ P, begin simp end
    , map_comp := begin intros, simp end
   }
  instance functor_prod
   : has_coe ((C₁ ⥤ C₂) × (C₃ ⥤ C₄)) ((C₁ × C₃) ⥤ (C₂ × C₄)) := ⟨prod_functor_of_functor_prod⟩ 
end product_coe
section product_adj 
  variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
            {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
            {E : Type u₃} [ℰ : category.{u₃ v₃} E]
  include 𝒞 𝒟 ℰ

  def product_adj : (C × D) ⥤ E → C ⥤ (D ⥤ E) := λ F,
  { obj := λ c,
    { obj := λ d, F.obj ⟨c,d⟩
    , map := λ d₁ d₂ f, F.map (𝟙, f)
    , map_id := λ d, begin rw [<-functor.map_id] end
    , map_comp := λ d₁ d₂ d₃ f g, begin rw [<-functor.map_comp], apply congr_arg, simp end
    }
  , map := λ c₁ c₂ f, nat_trans.mk (λ d, F.map ⟨f, 𝟙⟩) 
      begin intros d₁ d₂ g, simp [functor.map],  rw [<-functor.map_comp],  rw [<-functor.map_comp], simp  end
  , map_id := λ c, nat_trans.ext $ funext $ λ d,
      show F.map (𝟙 : (c,d) ⟶ (c,d)) = 𝟙_(F.obj (c, d)), by simp
  , map_comp := λ c₁ c₂ c₃ f g, nat_trans.ext $ funext $ λ d,
      show F.map ((f ≫ g, 𝟙) : (c₁,d) ⟶ (c₃,d)) = F.map ((f, 𝟙): (c₁,d) ⟶ (c₂,d)) ≫ F.map (g, 𝟙),
      begin rw <- functor.map_comp, apply congr_arg, simp end
  }

end product_adj

section op
  def op (C : Type*) := C
  variables {C : Type u₁} [𝒞 :category.{u₁ v₁} C]
  include 𝒞
  instance op_is_cat  : category.{u₁ v₁} (op C) :=
  { hom := λ X Y, @hom C (𝒞.to_has_hom) Y X -- just to make sure it's using the correct one
  , id := @has_id_comp.id C _
  , comp := λ X Y Z f g, @has_id_comp.comp C _ _ _ _ g f
  , id_comp := begin intros, simp end
  , comp_id := begin intros, simp end
  , assoc   := begin intros, simp end
  }
  #check @cat.op_is_cat
  attribute [simp] op
  attribute [simp] cat.op_is_cat
  notation C `ᵒᵖ` := op C
  @[inline] def hom_of_op_hom {X Y : op C} : hom (op C) X Y → hom C Y X := λ f, f
  @[inline] def op_hom_of_hom {X Y : op C} : hom (C) X Y → hom (op C) Y X := λ f, f
  @[simp] lemma op_hom_elim {Y X : op C} : 
    hom (op C) X Y = hom C Y X := rfl
  @[simp] lemma op_comp 
    {Z Y X : op C} {f : hom (op C) X Y} {g : hom (op C) Y Z}: 
    (@has_id_comp.comp (op C) _ _ _ _ f g) = @has_id_comp.comp C _ Z Y X (@hom_of_op_hom C _ Y Z g) (@hom_of_op_hom C _ X Y f) := rfl
  variables {D : Type u₂} [𝒟 :category.{u₂ v₂} D]
  include 𝒟
  
  def functor_op (F : C ⥤ D) : Cᵒᵖ ⥤ (Dᵒᵖ) :=
  { obj := λ c, F.obj c
  , map := λ X Y f,  F.map (f : hom C Y X)
  , map_id := begin intros, apply functor.map_id end
  , map_comp := begin intros, apply functor.map_comp end
  }
  notation F`ᵒᵖ` := functor_op F
end op

section unit
  instance unit_is_cat : category (unit) :=
  { hom := λ X Y, unit
  , id := λ X, ⟨⟩
  , comp := λ _ _ _ _ _, ⟨⟩
  , id_comp := begin intros, cases f, refl end
  , comp_id := begin intros, cases f, refl end
  , assoc := begin intros, cases f, cases g, cases h, refl end
  }
  inductive equaliser_shape : Type |A|B 
  inductive span_shape : Type |L | M | R

end unit

instance Sort_is_cat : category.{(u+1) (u)} (Type u) :=
{ hom := λ X Y, X → Y
, id := λ X x, x
, comp := λ X Y Z f g x, g (f x)
, id_comp := λ X Y f, rfl
, comp_id := λ X Y f, rfl
, assoc := λ X Y Z W f g h, rfl
}
@[simp] lemma Sort_is_cat_id {α : Type u} : (𝟙_α) = id := by refl
@[simp] lemma Sort_is_cat_comp {α β γ : Type u} {f : α ⟶ β} {g : β ⟶ γ} : (f ≫ g) = g ∘ f := by refl

def Hom {C : Type u} [𝒞 : category.{u v} C] : ((C ᵒᵖ) × C) ⥤ Type v :=
{ obj := λ P, hom C P.1 P.2
, map := λ P Q fg (p), fg.1 ≫ p ≫ fg.2
, map_id := begin intros, funext, simp, apply category.id_comp end
, map_comp := begin intros, funext, simp, refl end
}

section comma
  variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
            {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
            {E : Type u₃} [ℰ : category.{u₃ v₃} E]
  include 𝒞 𝒟 ℰ
  structure comma (F : C ⥤ E) (G : D ⥤ E) :=
  (o1 : C) (o2 : D) (f : F o1 ⟶ G o2)
  variables {F : C ⥤ E} {G : D ⥤ E}
  structure comma_hom (X Y : comma F G) :=
  (g1 : X.o1 ⟶ Y.o1)
  (g2 : X.o2 ⟶ Y.o2)
  (nat : F.map g1 ≫ Y.f = X.f ≫ G.map g2)
  def comma_hom.ext {X Y : comma F G} : Π {f g : comma_hom X Y}, f.g1 = g.g1 → f.g2 = g.g2 → f = g
  |⟨g1,g2,_⟩ ⟨_,_,_⟩ rfl rfl := rfl
  attribute [simp] comma_hom.nat
  instance comma.category : category (comma F G) :=
  { hom := λ X Y, comma_hom X Y
  , id := λ X, comma_hom.mk (𝟙) (𝟙) (by simp)
  , comp := λ X Y Z a b, ⟨a.g1 ≫ b.g1, a.g2 ≫ b.g2, begin simp, rw [<-category.assoc, comma_hom.nat], simp end⟩
  , id_comp := begin intros, simp, apply comma_hom.ext, simp end
  , comp_id := begin intros, simp, apply comma_hom.ext, simp end
  , assoc := begin intros, apply comma_hom.ext, simp, simp end
  }
end comma

section slice
    def slice (C : Type u₁) [category.{u₁ v₁} C] (Y : C) := Σ X : C, X ⟶ Y
    variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {X Y : C}
    include 𝒞
    notation C `/` X := slice C X
    instance slice.category : category (C / Y) :=
    { hom := λ A B, {f : A.1 ⟶ B.1 // f ≫ B.2 = A.2}
    , id := λ A, ⟨𝟙_A.1, by simp⟩
    , comp := λ f g h p q, ⟨p.1 ≫ q.1, by simp [p.2,q.2]⟩
    , id_comp := begin intros, simp end
    , comp_id := begin intros, simp end
    , assoc := begin intros, simp end
    }
    --@[simp] lemma slice.category_id {f : C / Y} : (@category.id (C / Y) _ f).1 = 𝟙 (f.1) := rfl
    --@[simp] lemma slice.category_comp {f g h : C / Y} {p : f ⟶ g} {q : g ⟶ h} : (p ≫ q).1 = p.1 ≫ q.1 := rfl
    def slice.forget : C / X ⥤ C := 
    { obj := λ f, f.1
    , map := λ f g p, p.1
    , map_id := begin intros, refl end
    , map_comp := begin intros, refl end
    }
end slice

section adjoint
  variables {C : Type u₁} {D : Type u₂} [𝒞 : category.{u₁ v₁} C] [𝒟 :category.{u₂ v₂} D]
  include 𝒞 𝒟
  class adjunction
    (L : C ⥤ D) (R : D ⥤ C) :=
    (unit       : functor.id C ⟹ (L ⋙ R))
    (counit     : (R ⋙ L) ⟹ functor.id D)
    (triangle_1 : ∀ X : D, (unit (R X)) ≫ (R.map (counit X)) = 𝟙_(R X))
    (triangle_2 : ∀ X : C, (L.map (unit X)) ≫ (counit (L X)) = 𝟙_(L X))
  attribute [simp] adjunction.triangle_1 adjunction.triangle_2
  --def adjunction_alt (L : C ⥤ D) (R : D ⥤ C) := -- [ERROR] This only works in small categories?
  --   ((Lᵒᵖ, D) ⋙ Hom) ⟷ ((Cᵒᵖ, D) ⋙ Hom)   -- It would be great if the parser could figure this out!
  infixr ` ⊣ `:70 := adjunction
  variables {L : C ⥤ D} {R : D ⥤ C} [L ⊣ R] {c : C} {d : D}
  /--Shorthand for unit of adjoint -/
  def adjunction.μ := adjunction.unit L R c
  /-- Shorthand for counit of adjoint -/
  def adjunction.ε := adjunction.counit L R d
  open adjunction
  def adjunction.φ : (c ⟶ R d) → (L c ⟶ d) := λ f, (L.map f) ≫ ε
  def adjunction.ψ : (L c ⟶ d) → (c ⟶ R d) := λ g, μ ≫ (R.map g)
  -- [TODO] show they are isos.
end adjoint

section alternative_adjoint
  -- another definition. In theory this one should be pithier but you have to hold the elaborator's hand. 
  def adj_alt {C D : Type u} [𝒞 : category.{u v} C] [𝒟 : category.{u v} D] (L : C ⥤ D) (R : D ⥤ C)
  :=
  --   ((Lᵒᵖ, D) ⋙ Hom) ⟷ ((Cᵒᵖ, D) ⋙ Hom)   -- It would be great if the parser could figure this out!
    have L3 : (((Cᵒᵖ) × D) ⥤ (Type v)) := @functor.comp ((Cᵒᵖ) × D) _ ((Dᵒᵖ) × D) _ (Type v) _ (Lᵒᵖ,functor.id D) (@Hom D 𝒟),
    have L4 : (((Cᵒᵖ) × D) ⥤ (Type v)) := @functor.comp ((Cᵒᵖ) × D) _ ((Cᵒᵖ) × C) _ (Type v) _ (functor.id (Cᵒᵖ), R) (@Hom C 𝒞),
    have category (((Cᵒᵖ) × D) ⥤ (Type v)) := begin apply @nat_trans.Hom_is_category end, 
    @iso _ this L3 L4
    -- [ERROR] the elaborator can't figure out that ((Cᵒᵖ) × D) ⥤ (Type v) is a category.
  -- def adj_of_adj_alt {C D : Type u} [𝒞 : category.{u v} C] [𝒟 : category.{u v} D] {L : C ⥤ D}{R : D ⥤ C}
  -- : adj_alt L R → adjunction L R := λ i, 
  --   { unit := {app := λ X, 
  --     begin cases i with φ ψ h₁ h₂, simp * at *, simp [has_hom.hom] at φ, 
  --     have φa : (L.obj X ⟶ L.obj X) → (X ⟶ R.obj (L.obj X)),
  --       apply @nat_trans.app, 
  --     have φa := φ.app (X, L.obj X),     end /- i.g.app (X,L.obj X) 𝟙 -/, naturality := sorry}
  --   , counit := {app := λ X, i.f.app (R.obj X, X) 𝟙, naturality := sorry}
  --   , triangle_1 := sorry
  --   , triangle_2 := sorry
  --   }
end alternative_adjoint

section simple_limits
    variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {X Y Z: C}
    include 𝒞

    notation X` ⇉ ` Y := (X ⟶ Y) × (X ⟶ Y)

    structure initial :=
    (O : C) (univ : ∀ (X : C), ∃! (o : O ⟶ X), true)

    structure equaliser (p: X ⇉ Y) :=
    (E : C) (e : E ⟶ X)
    (same : e ≫ p.1 = e ≫ p.2)
    (univ : ∀ (A : C) (f : A ⟶ X), (f ≫ p.1 = f ≫ p.2) → ∃! (k : A ⟶ E), k ≫ e = f) 

    structure pullback (f : X ⟶ Z) (g : Y ⟶ Z) :=
    (L : C)
    (π₁ : L ⟶ X)
    (π₂ : L ⟶ Y) 
    (square : π₁ ≫ f = π₂ ≫ g)
    (univ : ∀ (A : C) (a₁ : A ⟶ X) (a₂ : A ⟶ Y), (a₁ ≫ f) = (a₂ ≫ g) → ∃! (k : A ⟶ L), k ≫ π₁ = a₁ ∧ k ≫ π₂ = a₂)

    -- COLIMITS. I am just going to copy out the definitions because using Cᵒᵖ is masochistic.


    structure terminal :=
    (I : C) (univ : ∀ (X : C), ∃! (i : X ⟶ I), true)

end simple_limits

section set_function_cat
  
  /-- The category of functions on sets of α -/
  instance cat_of_set {α : Type u} : category (set α) :=
  {  hom := λ X Y, {x // x ∈ X} → {y // y ∈ Y}
  , id := λ X x, x
  , comp := λ X Y Z p q x, q $ p $ x
  , comp_id := begin intros, simp end
  , id_comp := begin intros, simp end
  , assoc := begin intros, simp end
  }

end set_function_cat

namespace free_cat
      def free (α : Type u) [hh :has_hom.{u v} α] := α

      variables {α : Type u} [hh : has_hom.{u v} α]
      include hh
      
      inductive fh : free α → free α → Type (max u v)
      |basic {a b : free α} : (@has_hom.hom α hh a b) → fh a b
      |id : Π {a}, fh a a
      |comp {a b c : free α} : fh a b → fh b c → fh a c
      open fh
      local infix ` ⇢ ` :70 := fh
      inductive hom_rel : Π {a b :free  α}, (a ⇢ b) → fh a b → Prop
      |comp_id {a b} {f : fh a b} : hom_rel (fh.comp f (id)) f
      |id_comp {a b} {f : fh a b} : hom_rel (fh.comp id f) f
      |assoc {a b c d} {f : fh a b} {g : fh b c} {h : fh c d} : hom_rel (fh.comp (fh.comp f g) h) (fh.comp f (fh.comp g h))
      |refl {a b} {f : a ⇢ b} : hom_rel f f
      |trans {a b} {f g h : a ⇢ b} : hom_rel f g → hom_rel g h → hom_rel f h
      |symm {a b} {f g : a ⇢ b} : hom_rel f g → hom_rel g f
      |congr {a b c} {f₁ f₂ : a ⇢ b} {g₁ g₂ : b ⇢ c} : hom_rel f₁ f₂ → hom_rel g₁ g₂ → hom_rel (fh.comp f₁ g₁) (fh.comp f₂ g₂) -- [?] do I actually need this one?


    def fhs (a b: free α) : setoid (fh a b) :=
    { r := λ f g, hom_rel f g
    , iseqv := ⟨λ f, hom_rel.refl,λ f g, hom_rel.symm,λ f g h, hom_rel.trans⟩
    }
    /-- The free category over some generating signature of homs. -/
    instance free_is_category {α : Type u} [hh : has_hom.{u v} α]: category.{u (max u v)} (free α) := 
    { hom := λ a b, quotient $ fhs a b
    , id := λ a, @quotient.mk (fh a a) (fhs a a) (@fh.id _ _ a)
    , comp := λ a b c f g, @quotient.lift_on₂ _ _ _ (fhs a b) (fhs b c) f g (λ (f : a⇢b) (g:b⇢c), @quotient.mk _ (fhs a c) $ fh.comp f g) 
        $ λ a₁ a₂ b₁ b₂ ab₁ ab₂, @quotient.sound _ (fhs a c) _ _ $ hom_rel.congr ab₁ ab₂
        --begin  apply hom_rel.congr   end
    , id_comp := begin intros, induction f, apply quotient.sound, apply hom_rel.id_comp, refl end
    , comp_id := begin intros, induction f, apply quotient.sound, apply hom_rel.comp_id, refl end
    , assoc := begin intros, induction f, induction g, induction h, apply quotient.sound, apply hom_rel.assoc, repeat {refl} end
    }
    instance {a b : α} : has_coe (@has_hom.hom α hh a b) (@has_hom.hom (free α) (free_cat.free_is_category.to_has_hom) a b)
    := ⟨λ x, @quotient.mk _ (fhs a b) $ fh.basic $ x⟩
    --export free [TODO] how to expose free?
end free_cat

namespace shape

  /-- The category `∙→∙` of two objects and one arrow. -/
  def two := set unit -- either ∅ or {*}
  instance : category (two) := cat.cat_of_set 

  inductive span_sig |A | B | X
  open span_sig
  inductive span_hom : span_sig → span_sig → Type
  |a : span_hom A X
  |b : span_hom B X
  instance : has_hom (span_sig) := ⟨λ Y Z, span_hom Y Z⟩
  def span := free_cat.free (span_sig)

end shape

section limit
  variables {J : Type u₁} [𝒥 : category.{u₁ v₁} J] {i j k: J} -- [TODO] non-small categories
  variables {C : Type u₂} [𝒞 : category.{u₂ v₂} C] {X Y Z: C}
  include 𝒥 𝒞
  /-- The constant diagram functor.  -/
  @[reducible] def Δ : C ⥤ (J ⥤ C) := 
  { obj := λ X,
    { obj := λ i, X
    , map := λ _ _ _, 𝟙
    , map_id := λ j, rfl
    , map_comp := by intros; simp
    }
  , map := λ X Y f,
    { app := λ _, f
    , naturality := λ i j ij, by simp
    }
  , map_comp := begin intros, apply nat_trans.ext, simp end
  , map_id := begin intros, apply nat_trans.ext, simp end
  }
  --@[simp] lemma wtf : (Δ.obj X: J ⥤ C) = {obj := λ i, X, map := λ i j ij, 𝟙 X,  map_id := λ j, rfl, map_comp := by intros; simp} := begin refl end
  -- @[simp] lemma Δ_def : (Δ : C ⥤ (J ⥤ C)) = product_adj (fst_functor) := rfl
  @[simp] lemma Δ_obj :(Δ.obj X).obj j = X := rfl
  @[simp] lemma Δ_map (ij : i ⟶ j) :(Δ.obj X).map ij = 𝟙 := rfl
  /-- The limit functor for a particular shape J. This is inhabited when the limit exists for all diagrams. -/
  class has_limits (J : Type u₁) [category.{u₁ v₁} J] (C : Type u₂) [category.{u₂ v₂} C] 
  := (Lim : (J ⥤ C) ⥤ C) (Δ_adj_Lim : Δ ⊣ Lim)

  structure cone (d : J ⥤ C) :=
  (peak : C)
  (legs : (Δ.obj peak) ⟶ d)

  def is_limit {d : J ⥤ C} (c : cone d) 
  := ∀ (A : C) (α : (Δ.obj A) ⟶ d), ∃! (e : A ⟶ c.peak), α = ((Δ.map e) ≫ c.legs)

  section preserves_etc
    variables {D : Type u₃} [𝒟 : category.{u₃ v₃} D]
    include 𝒟
    open has_limits
    def map_cone {d : J ⥤ C} (F : C ⥤ D) (l : cone d) : cone (d ⋙ F) :=
    {peak := F.obj l.peak
    , legs := 
      { app := λ j, begin cases l with Lc πc, apply F.map, apply πc.app end
      , naturality := begin intros i j ij, cases l, simp, rw [<-functor.map_comp, <-nat_trans.naturality], simp end
    }}
    variables (F : C ⥤ D) (d : J ⥤ C) 
    def preserves_limits := ∀ (l : cone d) (hl : is_limit l), is_limit (map_cone F l)
    def reflects_limits := ∀ (l : cone d) (hl : is_limit (map_cone F l)), is_limit l
    def creates_limits := ∀ (l : cone (d ⋙ F)), is_limit l → ∃ l' : cone d, l = map_cone F l' 
    
  end preserves_etc

end limit

section nat_cat
  instance nat_is_category : category (nat) :=
  { hom := λ n m, {s:unit // n ≤ m}
  , id := λ n, ⟨⟨⟩, by refl⟩
  , comp := λ i j k f g, ⟨⟨⟩, begin cases f, cases g, transitivity, assumption, assumption end⟩
  , id_comp:=  λ i k ⟨⟨⟩,f⟩, rfl
  , comp_id:= λ i k ⟨⟨⟩,f⟩, rfl
  , assoc := λ i j k l ⟨⟨⟩,f⟩ ⟨⟨⟩,g⟩ ⟨⟨⟩,h⟩, rfl
  }
end nat_cat


section simplicial
  def simplex := nat
  open nat

  def simp_comp_aux : list nat → list nat → nat → list nat → list nat
  |(0 :: t₁) t₂ n acc := simp_comp_aux t₁ t₂ 0 (n::acc)
  |((succ h₁) :: t₁) (h₂::t₂) n acc :=
     have h₁ < (succ h₁), begin apply lt_succ_of_le, apply le_of_eq, refl end,
     simp_comp_aux (h₁::t₁) t₂ (n+h₂) acc
  |_ _ n acc := acc

  #eval simp_comp_aux [3,0,1] [2,2,1,2] 0 []

  instance simplex_has_id_comp : has_id_comp simplex :=
  { hom := λ n m, {l : list nat // l.length = n ∧ list.foldr (+) 0 l = m} 
  , id := λ n, ⟨list.repeat 1 n, begin split, simp, induction n, simp, simp [n_ih] end⟩
  , comp := λ i j k f g, ⟨list.reverse $ simp_comp_aux f g 0 [], begin cases f with f fp, cases g with g gp, simp, sorry  end⟩
  }

  instance simplex_is_category : category (simplex) := {!!}

  -- inductive shom : simplex → simplex → Type 
  -- |d {n} : (fin (succ (succ n))) → shom (succ n) n -- face maps
  -- |s {n} : (fin (succ n)) → shom n (succ n) -- degeneracy maps. 
  -- |i {n} : shom n n
  -- |c {i j k} : shom i j → shom j k → shom i k
  -- open shom

  
  -- inductive srel {n m : simplex} : shom n m → shom n m → Prop
  -- |r1 {n i j}: i < j → srel (c (d i) (d (succ j))) (c (d j) (d i))
  -- |r2 {n i j} : i ≤ j → srel (c (s i) (s j)) (c (s (succ j)) (s i))
  -- |r3 {n i j} : i < j → srel (c (d (i) (succ j))) (c (s j) (d i))
  -- |r4 {n i j} : i = j → srel (c (d (i) (j))) shom.i
  -- |r5 {n i j} : i = j + 1 : srel (c (d (succ i) (j))) (c (s j) (d i))

end simplicial

/- [TODO] ideas for wasting time.

Sieves and Grotendiek Topologies

 -/

end cat