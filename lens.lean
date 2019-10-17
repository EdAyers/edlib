namespace category

universes u v

class distributive (F : Type u → Type u) extends functor F :=
(distribute : Π (G : Type u → Type u) [functor G] {α}, G(F α) → F(G α))
class traversable (T : Type u → Type u) extends functor T :=
(traverse : Π {M : Type u → Type u} [applicative M] {α β}, (α → M β) → (T α) → M (T β))
def list.traverse {M : Type u → Type u} [applicative M] {α β} (f : α → M β)  : list α → M (list β)
|(h::t) := pure list.cons <*> f h <*> list.traverse t
|[] := pure []
instance list_traversable : traversable list := ⟨λ M a α β f t, @list.traverse M a α β f t⟩
instance : traversable id := ⟨λ M i α β f a, f a⟩
class contrafunctor (F : Type u → Type u) :=
(contramap : Π {α β}, (α → β) → F β → F α)
class bifunctor (P : Type u → Type u → Type u) :=
(dimap {α β γ δ} : (α → β) → (γ → δ) → P β γ → P α δ)
(lmap {α β χ} : (α → β) → P β χ → P α χ := λ f, dimap f id)
(rmap {α β χ} : (α → β) → P χ α → P χ β := λ f, dimap id f)
class choice (P : Type u → Type u → Type u) extends bifunctor P :=
(left {α β : Type u} (γ : Type u) : P α β → P (α ⊕ γ) (β ⊕ γ))
(right {α β : Type u} (γ : Type u): P α β → P (γ ⊕ α) (γ ⊕ β))
class foldable (F : Type u → Type u) extends functor F := (fold {μ} [has_mul μ] [has_one μ] : F μ → μ)
instance arrow_is_choice : choice (→) :=
{ dimap := λ _ _ _ _ f g h, g ∘ h ∘ f
, left := λ α β γ f g, sum.rec_on g (sum.inl ∘ f) (sum.inr)
, right := λ α β γ f g, sum.rec_on g (sum.inl) (sum.inr ∘ f)
}
-- [TODO] lots of laws: https://hackage.haskell.org/package/lens-4.17/docs/Control-Lens-Prism.html#t:Choice
instance id_is_applicative : applicative id := {}
def functor.const (β : Type u) (α : Type u) : Type u := β
instance const_is_functor {β : Type u} : functor (functor.const β) :=
{map := λ α₁ α₂ f, id }
instance const_is_applicative {β : Type u} : applicative (functor.const $ option β) :=
{pure := λ α₁ a, none
, seq := λ α₁ α₂ f x, option.orelse f x}

section
    variables (σ τ α β : Type u)
    structure optic :=
    (r : Π {F : Type u → Type u}, (α → F β) → σ → F τ)
    structure iso :=
    (r : Π P F, bifunctor P → applicative F → P α (F β) → P σ (F τ))
    structure lens :=
    (r : Π {F : Type u → Type u} [functor F], (α → F β) → σ → F τ)
    structure prism :=
    (r : Π P F, choice P → applicative F → P α (F β) → P σ (F τ) )
    def prism' := prism σ σ α α
    def lens' := lens σ σ α α
    structure traversal :=
    (r :  Π (F : Type u → Type u), applicative F → (α → F β) → σ → F τ )
    def traversal' := traversal σ σ α α
    structure fold :=
    (r : Π {F : Type u → Type u} [contrafunctor F] [applicative F], (α → F α) → σ → F σ)
end

section
    variables {φ ψ σ τ α β : Type u}
    instance lens_of_optic : has_coe (optic σ τ α β) (lens σ τ α β) := ⟨λ o, ⟨λ F _ f s, o.r f s⟩⟩
    def traversal.of_lens : (lens σ τ α β) → (traversal σ τ α β) := λ o, ⟨λ F i f s, @lens.r _ _ _ _ o F i.to_functor f s⟩
    def optic.comp : optic φ ψ σ τ → optic σ τ α β → optic φ ψ α β
    |o₁ o₂ := ⟨λ F f, (o₁.r (o₂.r f))⟩

    def lens.make (view : σ → α) (set : σ → β → τ) : lens σ τ α β :=
    ⟨λ F i f s, @functor.map F i _ _ (set s) (f $ view $ s)⟩
    def lens.run_exp : lens σ τ α β → Π (F : Type u → Type u), (functor F) → (α → F β) → σ → F τ := @lens.r _ _ _ _

    def lens.view : lens σ τ α β → (σ → α) := λ o s, lens.run_exp o (functor.const α) category.const_is_functor id s
    def lens.set : lens σ τ α β → σ → β → τ := λ o s, lens.run_exp o (λ γ, β → γ) {map := λ γ δ f b, f ∘ b} (λ a, id) s

    def lens'.make (view : σ → α) (set : σ → α → σ) : lens' σ α := lens.make view set

    def prism.make_aux (review : β → τ) (discr : σ → τ ⊕ α)
        {P} {F} [choice P] [applicative F]
     :  P α (F β) → P σ (F τ)  := λ p,
             let j : τ ⊕ F τ → F τ := λ x, sum.rec_on x pure id in
             bifunctor.dimap discr j $ choice.right τ $ bifunctor.rmap (functor.map review) p
    def prism.make (review : β → τ) (discr : σ → τ ⊕ α) : prism σ τ α β := ⟨λ P F c a p, @prism.make_aux _ _ _ _ review discr P F c a p⟩
    def prism.review : prism σ τ α β → β → τ := λ ⟨r⟩ b, r (λ α β, β) id {dimap := λ _ _ _ _ _ f, f, left := λ _ _ _, sum.inl, right := λ _ _ _, sum.inr} {} b
    def prism.preview : prism σ τ α β → σ → option α := λ ⟨r⟩ s, r (→) (functor.const $ option α) category.arrow_is_choice category.const_is_applicative some s
    def traversal.of_prism : (prism σ τ α β) → (traversal σ τ α β) := λ ⟨r⟩, ⟨λ F a, r (→) F category.arrow_is_choice a⟩
    def traversal.comp : traversal φ ψ σ τ → traversal σ τ α β → traversal φ ψ α β
    |⟨t₁⟩ ⟨t₂⟩ := ⟨λ F a f s, t₁ F a (t₂ F a f ) s⟩
    def traversal.do : traversal σ τ α β → (α → β) → σ → τ := λ ⟨r⟩, r id {}
    def traversal.items {T : Type u → Type u} [c :traversable T] : traversal (T α) (T β) α β := ⟨λ F a, @traversable.traverse T c F a _ _⟩
    infixl ` ◾ ` : 100 := traversal.comp
    def folded_aux {F} [foldable F] {μ} [monoid μ] {T : Type u → Type u} [contrafunctor T] [applicative T] (f : α → T μ) : F α → T (F μ) :=
    begin
        intro,
        have hm : has_mul (T μ), apply has_mul.mk, exact λ x y, pure has_mul.mul <*> x <*> y,
        have ho : has_one (T μ), apply has_one.mk, apply pure, exact 1,
        have : F ( T μ ), apply functor.map f, assumption, apply_instance,
        have : T μ, refine @foldable.fold _ _ _ hm ho this,
        have : T (F μ), apply contrafunctor.contramap _ this, refine @foldable.fold _ _ _ _ _,
        exact this
    end


    def eg.fst : lens' (α × β) α := lens'.make prod.fst (λ ⟨_,b⟩ a, ⟨a,b⟩)
    def eg.snd : lens' (α × β) β := lens'.make prod.snd (λ ⟨a,_⟩ b, ⟨a,b⟩)
    def eg.nil : prism' (list α) punit := prism.make (λ _, []) (λ l, list.cases_on l (sum.inr ⟨⟩) (λ _ _, sum.inl l))
    def eg.cons : prism' (list α) (α × list α) := prism.make (λ ⟨h,t⟩, h::t) (λ l, list.cases_on l (sum.inl l) (λ h t, sum.inr ⟨h,t⟩))
    def eg.head : traversal' (list α) (α) := ((traversal.of_prism eg.cons) ◾ (traversal.of_lens eg.fst))
    #eval lens.view eg.fst (1,2)
    #eval lens.set eg.fst (1,2) 4
    #eval prism.review (@eg.nil ℕ) $ ⟨⟩
    #eval prism.review eg.cons $ ⟨4,[5,6]⟩
    #eval prism.preview eg.cons $ ( [5,4,5] : list nat)
    #eval traversal.do (traversal.items ◾ eg.head) (λ x : string, x ++ "_" ++ x) [["hello", "dingbat"], ["world"]]
    #eval traversal.do (traversal.items ◾ traversal.items) (λ x : string, x.length) [["hello", "d"], ["world"]]
    #eval traversal.do eg.head (λ x, x + x) ([4,5,6,7] : list ℕ)
end

end category