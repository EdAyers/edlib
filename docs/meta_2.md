# How `meta` works. Part 2: Induction

# Tactics for dealing with inductive datatypes

- `cases_core`


[TODO] from `tactic.lean`
- `subst` tactic
- `mk_id_eq`
- `mk_id_proof`

[TODO] from `simp_tactic.lean`
- `dunfold` vs `dsimp` vs `delta`? 
- What do `pre` and `post` do in `dsimp`?
- What is a discharger?
- What do all of the options in `simp_config` do?
- `simp`, what does it mean to dicharge? what exactly are simp lemmas? What are 
- Simp attributes minutiae such as `mk_simp_attr`

[TODO] `constructor_tactic.lean`.

[TODO] `init/meta/ref.lean`

[TODO] `%` antiquotation.

# interactive

- `loc` is either a 'wildcard', which means "everywhere", or a list of `option name`s. `none` means `target` and `some n` means `n` in the local context.