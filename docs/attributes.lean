/- 
# A list of all of the attributes that are in Lean that I have encountered.

- `@[elab_as_eliminator]`
- `@[simp]` When a lemma is tagged with `simp`, it becomes available to the `simp [*]` tactic.
- `@[derive decidable_eq]` will automatically ad
- `attribute [pp_using_anonymous_constructor] state_t`. Use this if your structure is a singleton and you want to skip the wrapper when you pretty print.


# A list of all of non-declarations in Lean

- `run_cmd` runs a `tactic _`. The tactic has a single goal `⊢ true`. 
- `set_option`
    + `pp.all`
    + ... [TODO] just the useful ones.
- `#check` 
- `#eval`  
- `#print` 


 -/