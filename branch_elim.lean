
/- Take a goal of the form `⊢ P(F(l))` where `l` is an inductive datatype
and `P` and `F` are defined on recursive datatypes.
Then `branch_elim F` will perform induction operations on variables until its definition goes away.
 -/

 /- 
 How it works:
 - find the first occurrence of `F` in the expression.
 - expand the definition of `F` and any `F._main` auxilary definitions.
 - perform induction and if splitting until all branches are accounted for.
 - [TODO] sometimes the same case will appear multiple times.
  -/

open tactic

/-- Replace the given name `n` with it's definition in the target expression. -/
meta def expand (n : name) : tactic unit :=
do
    delta_target [n]


