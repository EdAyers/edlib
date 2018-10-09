/- Copying out split_ifs from mathlib so I can understand it. -/

open expr tactic

namespace tactic
open interactive

-- meta def fold_test (e : expr) : tactic unit :=
--     trace $ expr.fold e [] (λ e n l, (e,n) :: l)
-- constant α : Type
-- constant f : α → α
-- example : true := 
-- begin
--   (to_expr ```(λ x : α, (λ y, x) $ f $ f x) >>= fold_test)
-- end

/-- Returns the condition of a  -/
meta def find_if_cond : expr → option expr | e := -- note the `| e` style.
e.fold none $ λ e _ acc, acc <|> do
    c ← match e with
        | `(@ite %%c %%_ _ _ _) := some c
        | `(@dite %%c %%_ _ _ _) := some c
        | _ := none
        end,
    guard ¬c.has_var,
    find_if_cond c <|> -- Why does this need to be recursive?
    return c 

/-- Find an if condition at one of the locations. -/
meta def find_if_cond_at (at_ : loc) : tactic (option expr) := do
lctx ← at_.get_locals, -- get the local context
lctx ← lctx.mmap infer_type, --get the types
tgt ← target,
let es := if at_.include_goal then tgt::lctx else lctx,
pure $ find_if_cond $ es.foldr app (default expr) -- jam all of the terms into one giant expression and run find_if_cond on it.

-- make a new simp attribute called "split_if_reduction"
run_cmd mk_simp_attr `split_if_reduction
-- Add "split_if_reduction" attributes to these if-reductions
attribute [split_if_reduction] if_pos if_neg dif_pos dif_neg

meta def reduce_ifs_at (at_ : loc) : tactic unit := do
sls ← get_user_simp_lemmas `split_if_reduction,
let cfg : simp_config := { fail_if_unchanged := ff },
let discharger := assumption <|> (applyc `not_not_intro >> assumption),
hs ← at_.get_locals, 
hs.mmap' (λ h, simp_hyp sls [] h cfg discharger >> skip),
when at_.include_goal (simp_target sls [] cfg discharger)

/-- Perform an if-split with the condition `c`, give the new hypothesis the name `n`. -/
meta def split_if1 (c : expr) (n : name) (at_ : loc) : tactic unit := 
by_cases c n *> reduce_ifs_at at_

/--Pull a name from a ref list and use that, otherwise get a boring fresh name. -/
private meta def get_next_name (names : ref (list name)) : tactic name := do
ns ← read_ref names,
match ns with
| [] := get_unused_name `h
| (n::ns) := do write_ref names ns, return n 
end

/-- Check that the given condition isn't already in the local context. -/
private meta def value_known (c : expr) : tactic bool :=
(find_assumption c $> tt)
<|> (find_assumption `(¬%%c) $> tt)
<|> (pure ff)

private meta def split_ifs_core (at_: loc) (names : ref (list name)) : list expr → tactic unit := λ done, do
some cond ← find_if_cond_at at_ | fail "no ite or dite expressions found",
let cond := match cond with `(¬%%p) := p | p := p end, -- strip off the ¬
if cond ∈ done then skip else do -- skip conditions which have already been done.
no_split ← value_known cond,
if no_split then do
    reduce_ifs_at at_,
    try (split_ifs_core (cond :: done)) 
else do
    n ← get_next_name names, -- pull a new name off the shelf.
    split_if1 cond n at_,
    try (split_ifs_core (cond :: done))

meta def split_ifs (names : list name) (at_ : loc := loc.ns [none]) /-by default do the target.-/ :=
using_new_ref names $ λ names, split_ifs_core at_ names []

namespace interactive
open interactive.types
/-- Splits all if-then-else-expressions into multiple goals.

Given a goal of the form `g (if p then x else y)`, `split_ifs` will produce
two goals: `p ⊢ g x` and `¬p ⊢ g y`.

If there are multiple ite-expressions, then `split_ifs` will split them all,
starting with a top-most one whose condition does not contain another
ite-expression.

`split_ifs at *` splits all ite-expressions in all hypotheses as well as the goal.

`split_ifs with h₁ h₂ h₃` overrides the default names for the hypotheses.
-/
meta def split_ifs (at_ : parse location) (names : parse with_ident_list) : tactic unit :=
tactic.split_ifs names at_

end interactive
end tactic