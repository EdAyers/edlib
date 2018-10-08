import .order

namespace rb
universes u v w
inductive col |Red|Black
inductive node (k : Type u) (α : Type v) : Type max u v
|Leaf {}: node
|Node (c:col) (l:node) (v:k×α) (r:node) : node
open node col
notation `Rd` := (Node Red)
notation `Bk` := (Node Black)

namespace node
variables {k : Type u} [has_lt k] [decidable_rel ((<) : k → k → Prop)]
variables {α : Type v}

def empty : node k α := Leaf
instance : has_emptyc (node k α) := ⟨empty⟩

def mk_black : node k α → node k α
|(Leaf) := Leaf
|(Node _ l a r) := Node Black l a r

def mk_red : node k α → node k α 
|Leaf := Leaf
|(Node _ l a r) := Node Red l a r


@[simp] def lbal : node k α → k×α → node k α → node k α
| (Rd (Rd a x b) y c) v r := Rd (Bk a x b) y (Bk c v r)
| (Rd a x (Rd b y c)) v r := Rd (Bk a x b) y (Bk c v r)
| l v r := Bk l v r

variables (a b c r : node k α) (x y v : k×α)

def rbal : node k α → k×α → node k α → node k α
| l v (Rd (Rd b w c) z d) := Rd (Bk l v b) w (Bk c z d)
| l v (Rd b w (Rd c z d)) := Rd (Bk l v b) w (Bk c z d)
| l v r := Bk l v r

/--Same as `rbal` but cases swapped.-/
def rbal' : node k α → k×α → node k α → node k α
| l v (Rd b w (Rd c z d)) := Rd (Bk l v b) w (Bk c z d)
| l v (Rd (Rd b w c) z d) := Rd (Bk l v b) w (Bk c z d)
| l v r := Bk l v r

def lbalS : node k α → k×α → node k α → node k α
 | (Rd a x b) v r := Rd (Bk a x b) v r
 | l v (Bk a w b) := rbal' l v (Rd a w b)
 | l v (Rd (Bk a w b) z c) := Rd (Bk l v a) w (rbal' b z (mk_red c))
 | l v r := Rd l v r /- impossible -/

def rbalS : node k α → k×α → node k α → node k α
| l v (Rd b w c) := Rd l v (Bk b w c)
| (Bk a v b) w r := lbal (Rd a v b) w r
| (Rd a v₁ (Bk b v₂ c)) v₃ r := Rd (lbal (mk_red a) v₁ b) v₂ (Bk c v₃ r)
| l v r := Rd l v r /- impossible -/

def ins_aux (key : k) (x : α) : node k α → node k α 
|Leaf := Rd Leaf ⟨key,x⟩ Leaf
|(Bk l v r) :=
    if key < v.1 then lbal (ins_aux l) v r
    else if key > v.1 then rbal l v (ins_aux r)
    else Bk l ⟨key,x⟩ r
|(Rd l v r) :=
    if key < v.1 then Rd (ins_aux l) v r
    else if key > v.1 then Rd l v (ins_aux r)
    else Rd l ⟨key,x⟩ r

def insert : k → α → node k α → node k α := 
λ key x s, mk_black (ins_aux key x s)
instance : has_insert (k×α) (node k α) := ⟨λ ⟨key,a⟩ t, insert key a t⟩ 

/--Used to get the `append` method to be well-founded-/
instance custom_wf : has_well_founded (node k α × node k α) := 
has_well_founded_of_has_sizeof (node k α × node k α) 

def append : (node k α × node k α) → node k α
|⟨Leaf, r⟩ := r
|⟨ l,  Leaf⟩  := l
|⟨(Rd ll lx lr),(Rd rl rx rr) ⟩ :=
    match append ⟨lr, rl⟩ with
    |Rd lr x rl := Rd (Rd ll lx lr) x (Rd rl rx rr)
    |lrl := Rd ll lx (Rd lrl rx rr)
    end
|⟨ (Bk ll lx lr) ,(Bk rl rx rr) ⟩ :=
    match append ⟨lr, rl⟩ with
    |Rd lr x rl := Rd (Bk ll lx lr) x (Bk rl rx rr)
    |lrl := lbalS ll lx (Bk lrl rx rr)
    end
|⟨(Rd ll lx lr), r⟩ :=  Rd ll lx (append ⟨lr, r⟩)
|⟨ l, (Rd rl rx rr)⟩ := Rd (append ⟨l, rl⟩) rx rr

def erase_aux (key : k) : node k α → node k α
|Leaf := Leaf
|(Node _ l y r) :=
    if key < y.1 then
        match l with
        | (Bk _ _ _) := lbalS (erase_aux l) y r
        | _ := Rd (erase_aux l) y r
        end
    else if key > y.1 then
        match r with
        | (Bk _ _ _) := rbalS l y (erase_aux r)
        | _ := Rd l y (erase_aux r)
        end
    else append ⟨l, r⟩

def erase (key : k) (t : node k α) : node k α := 
mk_black (erase_aux key t)

def pop_min_aux : node k α → k×α → node k α → k × α × node k α
|Leaf ⟨k,x⟩ r := ⟨k,x,r⟩
|(Node lc ll lx lr) y r :=
    let ⟨k,x,l⟩ := pop_min_aux ll lx lr in
    match lc with
    |Black := ⟨k,x, lbalS l y r⟩
    |Red := ⟨k,x, Rd l y r⟩
    end

/-- Remove the minimal element and key from the table. -/
def pop_min : node k α → option (k × α × node k α)
|Leaf := none
|(Node _ l y r) :=
    let ⟨k,x,t⟩ := pop_min_aux l y r in
    some ⟨k,x, mk_black t⟩

def fold {β : Type w} (f : k → α → β → β) : β → node k α → β 
|b Leaf := b
|b (Node _ l ⟨k,a⟩ r) := fold (f k a $ fold b l) r

def mfold {T : Type u → Type u} [monad T] {β} 
  (f : k → α → β → T β) : β → node k α → T β
|b Leaf := pure b
|b (Node _ l ⟨k,a⟩ r) := do
    b ← mfold b l,
    b ← f k a b,
    mfold b r
/-- Get the number of black nodes between the root and the leaves of the trees. -/
def height : node k α → ℕ
|Leaf := 0
|(Rd l _ _ ) := height l
|(Bk l _ _ ) := nat.succ $ height l


namespace treeify 
    def bogus : node k α × list (k×α) := ⟨Leaf, []⟩
    def treeify_t (k : Type u) (α : Type v) : Type max u v := list (k×α) → (node k α × list (k×α))
    def treeify_zero : treeify_t k α := λ acc, ⟨Leaf, acc⟩
    def treeify_one : treeify_t k α 
    |(x::acc) := ⟨Rd Leaf x Leaf, acc⟩
    |_ := bogus
    def treeify_cont (f g : treeify_t k α) : treeify_t k α :=
    λ acc, match f acc with
    |⟨l, x::acc⟩ := let ⟨r, acc⟩ := g acc in ⟨Bk l x r, acc⟩
    |_ := bogus
    end
    def positive := list bool
    def treeify_aux : bool → positive → treeify_t k α
    |pred [] := if pred then treeify_zero else treeify_one
    |pred (ff::n) := treeify_cont (treeify_aux pred n) (treeify_aux tt n)
    |pred (tt::n) := treeify_cont (treeify_aux ff n) (treeify_aux pred n)
    def succ : positive → positive 
    |[] := [ff]
    |(ff::tail) := tt::tail
    |(tt::tail) := ff :: (succ tail)
    def plength_aux : list α → positive → positive
    |[] p := p
    |(_::t) p := plength_aux t $ succ p
    def plength (l : list α) := plength_aux l []
end treeify
/--Take an __ordered__ list and convert it to a node tree.-/
def treeify (l : list (k×α)) : node k α := 
prod.fst $ treeify.treeify_aux tt (treeify.plength l) l

def filter (p : k → α → bool) : node k α → node k α := 
treeify ∘ fold (λ key a l, ite (p key a) (⟨key,a⟩::l) l) []

def get (key:k) : node k α → option α
|Leaf := none
|(Node _ l y r) :=
    if key < y.1 then get l else
    if y.1 < key then get r else
    some (y.2)

def contains (key:k): node k α → bool
:= option.is_some ∘ get key

instance : has_mem (k) (node k α) := ⟨λ key t, contains key t⟩

def min : node k α → option (k×α)
|Leaf := none
|(Node _ l x _) := (min l) <|> some x
def max : node k α → option (k× α ) 
|Leaf := none
|(Node _ _ x r) := (max r) <|> some x

/-- Asssign each member of `r` to `l`, if there is a key clash then choose the entry in `r` and clobber `l`. -/
def merge  : node k α → node k α → node k α := fold insert

def table (k : Type u) : Type u := node k unit

def intersect (t₁ t₂ : table k) : table k :=
    if height t₁ < height t₂ 
    then filter (λ k _, contains k t₂) t₁
    else filter (λ k _, contains k t₁) t₂
instance : has_inter (table k) := ⟨intersect⟩ 

def union (l r : table k) : table k :=
    if height l < height r 
    then fold insert r l
    else fold insert l r
instance : has_union (table k) := ⟨union⟩

/--Remove all of the keys found in the table `r` from the dictionary `l`. -/
def subtract (l : node k α) (r : table k) : node k α := fold (λ k _ l, erase k l) l r
--instance : has_sub (table k) := ⟨subtract⟩

def map {β : Type w} (f : α → β) : node k α → node k β
|Leaf := Leaf
|(Node c l ⟨k,a⟩ r) := Node c (map l) ⟨k, f a⟩ (map r)
instance : functor (node k) :=
{ map := λ _ _ f t, map f t
}
def keys_of : (node k α) → table k := map (λ a, ⟨⟩)
end node

namespace proofs
open nat node
variables {k : Type u} {α : Type v}
variables [decidable_linear_order k]
inductive is_rb : node k α → col → nat → Prop
|leaf_rb {} : is_rb Leaf Black 0
|red_rb {l v r n} (rb_l : is_rb l Black n) (rb_r : is_rb r Black n) : is_rb (Rd l v r) Red n
|black_rb {l c₁ v r c₂ n} (rb_l : is_rb l c₁ n) (rb_r : is_rb r c₂ n) : is_rb(Bk l v r) Black (succ n)

inductive mem (key:k) : node k α → Prop
|left {c l v r} : mem l → mem (Node c l v r)
|mid {c l v r} : (v:k×α).1 = key → mem (Node c l v r)
|right {c l v r} : mem r → mem (Node c l v r)
instance : has_mem (k) (node k α) := ⟨mem⟩
lemma leaf_empty {key : k} : key ∉ (@Leaf k α) := λ h, by cases h

def dominates (k₁ : k) (t : node k α) : Prop
:= ∀ k₂ ∈ t, k₁ > k₂
def dominated_by (k₁ : k) (t : node k α) : Prop
:= ∀ k₂ ∈ t, k₁ < k₂
infix ` ⋗ `: 50 := dominates
infix ` ⋖ `: 50 := dominated_by

inductive ordered : node k α → Prop
|o_leaf {} : ordered (Leaf) 
|o_node {c l} {v:k×α} {r} (ol:ordered l) (vdl :  v.1 ⋗ l) (rdv : v.1 ⋖ r) (or : ordered r) : ordered (Node c l v r)
open ordered
@[simp] def is_wf (t: node k α) :  Prop := (∃ n, is_rb t Black n) ∧ ordered t

/- [TODO] 
These things are way too tedious to work with manually proving.
Instead I need to make a tactic which looks at the structure of lbal and automatically solves / emits subgoals for each case.
What does this mean?
- Figure out the cases of `l` and `r` that are needed to eliminate lbal. Do this recursively.
- The goal is to rewrite the inside of `ordered(-)` so it has the form _Leaf_ or _Node_, because we know that this is going to be the only way of solving ordered.
- Then break up ordered. The trick is knowing when you can stop because you have an assumption.
- This is similar to how split-ifs works so I should take a look at how that is implemented.

So, `split_matches lbal` takes the inductive definition of `lbal`, and keeps performing 'by induction' steps on the arguments to `lbal` until 
the induction steps in `lbal`'s definition are all reduced.
I think this is completely doable in a few day's work.

-/

variables {key k₁ k₂ :k} {a:α} {v v₁ v₂ : k × α} {l r t : node k α} {c : col}

@[trans] lemma dominates.trans : k₁ > k₂ → k₂ ⋗ t → k₁ ⋗ t
:= λ p q k₃ kt, lt.trans (q _ kt) p 
lemma dominates.leaf : k₁ ⋗ (@Leaf k α) := λ k₂ kt, false.rec_on _ $ leaf_empty kt
lemma dominates.node (hl : k₁ ⋗ l) (hv : k₁ > v.1) (hr : k₁ ⋗ r) : k₁ ⋗ (Node c l v r)
|k₂ (mem.left xl) := hl _ xl
|k₂ (mem.mid xm) := xm ▸ hv
|k₂ (mem.right xr) := hr _ xr
lemma dominates.l : k₁ ⋗ (Node c l v r) → k₁ ⋗ l := λ h k₂ hl, h k₂ (mem.left hl)
lemma dominates.r : k₁ ⋗ (Node c l v r) → k₁ ⋗ r := λ h k₂ hr, h k₂ (mem.right hr)
lemma dominates.v : k₁ ⋗ (Node c l v r) → k₁ > v.1 := λ h, h v.1 $ mem.mid rfl
@[trans] lemma dominated_by.trans : k₁ < k₂ → k₂ ⋖ t → k₁ ⋖ t
:= λ p q k₃ kt, lt.trans p (q _ kt)
lemma dominated_by.leaf : k₁ ⋖ (@Leaf k α) := λ k₂ kt, false.rec_on _ $ leaf_empty kt
lemma dominated_by.node (hl : k₁ ⋖ l) (hv : k₁ < v.1) (hr : k₁ ⋖ r) : k₁ ⋖ (Node c l v r)
|k₂ (mem.left xl) := hl _ xl
|k₂ (mem.mid xm) := xm ▸ hv
|k₂ (mem.right xr) := hr _ xr
lemma dominated_by.l : k₁ ⋖ (Node c l v r) → k₁ ⋖ l := λ h k₂ hl, h k₂ (mem.left hl)
lemma dominated_by.r : k₁ ⋖ (Node c l v r) → k₁ ⋖ r := λ h k₂ hr, h k₂ (mem.right hr)
lemma dominated_by.v : k₁ ⋖ (Node c l v r) → k₁ < v.1 := λ h, h v.1 $ mem.mid rfl

def all_below := λ (t₁ t₂ : node k α), ∀ (k₁ ∈ t₁) (k₂ ∈ t₂), k₁ < k₂
infix ` ⊏ `: 100 := all_below

open tactic

/- Look at the target, find all occurences of the name,  -/

meta def expand (n : name) : tactic unit := 
do delta_target [n]

meta def get_cases_candidate_single (e : expr) : tactic expr :=
do
    --e ← tactic.to_expr pe,
    s_l ← get_simp_lemmas_or_default none,
    e ← simp_lemmas.dsimplify s_l [`rec_on, `cases_on] e {fail_if_unchanged := ff}, -- rewrite alternative definitions of recursion.
    --e ← whnf e,
    (fn,args) ← pure $ expr.get_app_fn_args e,
    fn_name ← pure $ expr.const_name fn,
    env ← get_env,
    is_rec ← pure $ environment.is_recursor env fn_name,
    -- hopefully, the last argument of the recursor is always the thing being recursed on.
    rec_arg ← pure $ expr.app_arg e,
    is_local ← pure $ expr.is_local_constant rec_arg,
     trace fn_name,
    -- trace args,
    -- trace is_rec,
    -- trace rec_arg,
    -- trace is_local,
    -- trace "\n",
    guard is_rec,
    guard is_local, 
    pure rec_arg

meta def get_cases_candidate : expr → tactic expr := λ e,
get_cases_candidate_single e <|> list.any_of (expr.get_app_args e) get_cases_candidate


meta def recursion_cases : tactic unit :=
do
    t ← target >>= instantiate_mvars,
     cand ← get_cases_candidate t,
     --trace cand,
     tactic.cases_core cand,
     --dsimp_target none [] {fail_if_unchanged := ff},
     all_goals $ try $ dsimp_target,
     --(dsimp_target none []) <|> pure ⟨⟩,
    --  args ← pure $ expr.get_app_args e,
    --  list.any_of args cases_on_variable
    --tactic.dsimplify (λ e, pure ⟨e,tt⟩) (dsimp_post) t,
    pure ⟨⟩

#check node.cases_on
#check node.rec_on

meta def cases_all : expr → tactic (list expr) := λ h,
do 
    --h ← get_local h_name,
    --trace h,
    ty ← infer_type h >>= instantiate_mvars >>= whnf,
    --trace ty,
    --[c] ← get_constructors_for ty | pure [],
    -- count the number of non-named arguments
    [(case_name,new_hyps,new_subs)] ← cases_core h | fail "more than one constructor",
    list.mfoldl (λ l h, list.append l <$> ((cases_all h) <|> (pure [h]))) [] new_hyps

meta def one_of : list (tactic unit) → tactic unit
|(h::t) := h <|> one_of t
|[] := skip

meta def apply_pexpr : pexpr → tactic unit :=
λ p, ((to_expr p) >>= apply) $> ⟨⟩

lemma rbal_ind {P Q : node k α → Prop} {q : Q r}
    (c₁ : Π  {b c d w z}, Q(Rd (Rd b w c) z d) → P(Rd (Bk l v b) w (Bk c z d)))
    (c₂ : Π  {b c d w z}, Q(Rd b w (Rd c z d)) → P(Rd (Bk l v b) w (Bk c z d)))
    (c₃ : P(Bk l v r))
    : P(rbal l v r)
    := 
    begin
        expand ``rbal, dsimp_target none [`id_rhs],
        repeat{one_of [
            recursion_cases,
            apply_pexpr ```(c₁ q),
            apply_pexpr ```(c₂ q),
            apply_pexpr ```(c₃)  
        ]},
    end

lemma rbal_ordered (ol : ordered l) (vdl : v.1 ⋗ l) (rdv : v.1 ⋖ r) (or : ordered r) : ordered (rbal l v r) :=
begin
   apply rbal_ind, apply and.intro or rdv,
   focus {
        intros _ _ _ _ _ a, (get_local `a >>= cases_all), apply o_node (o_node _ _ _ _) _ _ (o_node _ _ _ _), repeat {assumption},
        apply a_right.l.l, 
        apply dominates.node, apply dominates.trans, apply a_right.l.v, assumption, apply a_right.l.v, assumption,
        apply dominated_by.node, assumption, apply a_left_vdl.v, apply dominated_by.trans, apply a_left_vdl.v, assumption, apply a_left_vdl.r
      },
    focus {
        intros _ _ _ _ _ a, (get_local `a >>= cases_all), apply o_node (o_node _ _ _ _) _ _ (o_node _ _ _ _), repeat {assumption},
        apply a_right.l,
        apply dominates.node, apply dominates.trans, apply a_right.v, assumption, apply a_right.v, assumption,
        apply dominated_by.node, apply a_left_rdv.l, apply a_left_rdv.v, apply dominated_by.trans, apply a_left_rdv.v, assumption
    },
    focus {
        apply o_node ol vdl rdv or, 
    }
end

lemma rbal_mem : (key ∈ r) → (key ∈ rbal l v r) := begin 
    intros,
    apply rbal_ind, apply a, focus {intros _ _ _ _ _ h, cases h, cases h_a, 
        apply (mem.left $ mem.right _),assumption, 
        apply (mem.mid _), assumption,
        apply (mem.right $ mem.left _), assumption,
        apply (mem.right $ mem.mid _), assumption,
        apply (mem.right $ mem.right _), assumption,
    }, 
    focus {intros, cases a_1,
        apply (mem.left $ mem.right _), assumption,
    apply (mem.mid _), assumption,
    cases a_1_a,
    apply (mem.right $ mem.left _), assumption,
    apply (mem.right $ mem.mid _), assumption,
    apply (mem.right $ mem.right _), assumption,
     },
    focus {
        apply mem.right, assumption,
    }
end

lemma rbal_rb {cl cr n} : is_rb l cl n → is_rb r cr n → ∃ c', is_rb (rbal l v r) c' (succ n) := 
begin
 intros lrb rrb, apply @rbal_ind k _ _ _ _ _  (λ t, ∃ c', is_rb (t) c' (succ n)) (λ t, is_rb t cr n), apply rrb, 
 focus {intros, cases a, cases a_rb_l, },  
 focus {intros, cases a, cases a_rb_r, },
 focus {existsi Black, apply is_rb.black_rb, assumption, assumption}
end

-- [TODO] repeat for lbal.

lemma lbal_rb {cl cr n} : is_rb l cl n → is_rb r cr n → ∃ c', is_rb (lbal l v r) c' (succ n) := sorry
lemma ins_aux.is_rb {n} : is_rb t c n → ∃ c', is_rb (ins_aux key a t) c' n := sorry
lemma ins_aux.ordered : ordered t → ordered (ins_aux key a t) := sorry

/- Now that I have worked this out, 
I am 100% sure that I can write some automation for this, probably in the same vain as auto2
 so I don't have to redesign anything.
   It will be some non-trivial amount of work.
 -/

lemma empty_is_wf : is_wf (@node.empty k _ _ α) := sorry

lemma insert_is_wf :is_wf t → is_wf (insert key a t) := sorry
lemma insert_works :  is_wf t → get key (insert key a t) = some a := sorry

lemma erase_is_wf : is_wf t → is_wf (erase key t) := sorry 
lemma erase_works : is_wf t → get key (erase key t) = none := sorry

/- [TODO] from mathlib -/
inductive sorted (R : α → α → Prop) : list α → Prop
|nil {} : sorted []
|cons {a} {l:list α} : (∀ b∈l, R a b) → sorted l → sorted (a::l)
lemma treeify_works : ∀ {l : list (k×α)}, sorted ((<) on prod.fst) l → is_wf (treeify l) := sorry
lemma filter_works {p} : is_wf t → is_wf (filter p t) := sorry

end proofs
end rb



