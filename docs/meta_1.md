# How `meta` works. Part 1: Tactics

## How tactics work.

I would first like to remind everyone that I have massively simplified how Lean actually works to the point that the Lean developers will cringe when they read this.
My goal is to give a kind of working abstraction that tactic writers can use to reason about how Lean will behave.

Suppose that we are trying to construct a valid `expr` of a certain type `T` using tactics. If `T : Prop`, then this is the same task as proving the statement `T`. 
We might start by writing (say):
```lean
lemma my_lemma (p q r : Prop) : (p → q → r) → (p → q) → p → q × r := 
begin
  <cursor goes here>
end
```

At this point, if you open the _Display Goal_ viewer in your editor, you will see:  
```lean
p q r : Prop
⊢ (p → q → r) → (p → q) → p → q × r
```

This is Lean's `tactic_state`. When you plant your cursor in the `begin` block (or on a placeholder "`_`"), Lean knows that you are trying to create an `expr` which typechecks to `∀ (p q r : Prop), (p → q → r) → (p → q) → p → q × r`.
We don't always know how to write down an `expr` straight away, so instead we want to build the `expr` from the root up, and the bits that we haven't finished yet are left as 'holes' that we promise to figure out later.
These holes are called __metavariables__, a metavariable is an `expr` that will be filled in with a proper `expr` later.

Another new concept we need are __local constants__. These are all of the things to the left of the `⊢` in the tactic state. In our case `p`,`q` and `r`. Local constants are the same as regular `const` `expr`s, but they only exist in our current scope.

```lean
inductive expr := 
| ... stuff from before ...
|mvar (pretty_name : name) (unique_name : name) (type : expr) : expr
|local_const (pretty_name : name) (unique_name : name) (type : expr) : expr
```
([TODO] should I add `binder_info`?)
Note how `mvar`  has a `type` argument. That means that we can run an `expr` containing metavariables through the kernel type-checker, and it will still be able to say what the type of the `expr` is, but it will not count as a valid `expr` until all of the `mvar`s are replaced with other valid `expr`s of the correct type. The type argument on the `mvar` may _itself_ contain other `mvars`. 

The `pretty_name` is what you see in the output window, the `unique_name` is used internally to uniquely identify the `mvar` or `local_const`. Lean has both names because the unique names would make the output window look cluttered.

So, when you plonk your cursor in the `begin` block. Lean makes a `tactic_state`. The `tactic_state` is comprised of the following pieces of data: (in Lean3's C++, the place to look at is `src/library/tactic/tactic_state.h`)
- The __environment__. In our example it would be the environment created by all of the Lean code before this `lemma`.
- A __local context__. To be discussed below.
- A __metavariable context__. To be discussed below.
- An `expr` called the __result__, that depends on the metavariables and local constants given in the respective contexts above. This is usually hidden from the user.
- A list of __goals__, these are just a selection of metavariables from the context that we particularly care about. We refer to the head of this list to be the __main goal__.
- Some nitpicky settings that I won't talk about here. There are also some special mechanisms for typeclasses that I will gloss over. [TODO] `set_options`, `get_options`

### The local context

The local context is a dictionary of __local declarations__ indexed by `name`. A local declaration holds on to the following data:
- The `unique_name`, `pretty_name` and `type` as found in the `local_const` constructor for `expr`.
- `value : option expr` containing a possible expansion of the local constant. So for example you might have a local definition in the context. You can see one of these if you write `let x := f(y),` in the tactic block.

So when your `expr` contains a `local_const n _ _`, Lean figures out what that `local_const` is by looking up it's unique name `n` in the local context.

### The metavariable context

Similarly, a metavariable context has a dictionary of __metavariable declarations__. A metavariable declaration holds on to the following data;
- A snapshot of the local context in which the metavariable was created. Our metavariable is only allowed to depend on these local constants.
- An `expr`, giving the type of the metavariable.

The metavariable context also has an __assignments__ dictionary of `expr`s indexed by `name`. Once a metavariable gets assigned -- i.e. the hole is _filled_ by another `expr` -- the `expr` it is assigned is stored in here.
If we try to assign the expression `t` to the metavariable `m`, it will fail when:

- It already has an entry in the assignments table.
- The types are not equal. [TODO] up to matching? unify? Is it always true that if `t`'s type mentions `m`, then `t` must also mention `m`?
- `t` depends on `m`.
- `t` depends on a local constant that is not in `m`'s local context snapshot.
- `t` depends on a different metavariable `m2` and `m2` has already been assigned with a term that depends on `m`. [TODO] I think you don't have to search further than 1 away, because I think that when `m2` is assigned all of the assignment's metavariables are instantiated.
It's important to rember that just because a metavariable has been _assigned_ -- that is, has an entry in the assignments table -- that metavariable won't be magically removed from all of the expressions that depend on it. We say an expression `t` has been __instantiated__ with `m` when all of the occurrences of `m` in `t` have been replaced with its assignment.

Similarly, there is also an assignments dictionary for type universe (`level`) metavariables.

### The tactic state lifecycle

Now let's go back to putting the cursor in the `begin` block. Lean then initialises the tactic state as follows.
- Any argument of the lemma (stuff which looks like `(x : α)` before the `:=`) gets added to the local context.
- Any names in a `variables` declaration that appear somewhere in the type definition or arguments are added to the local context.
- Any implicit typeclass instances used are added to the local context. (TODO the rules around when typeclasses are added seems quite finicky).
- A fresh metavariable `M` is created.
- The `result` of the tactic state is set to be `M`.
- The `goals` are set to be `[M]`.

The picture to keep in mind is that of a growing tree (or coral reef?), where the tips of the growth are metavariables, we grow the tree by replacing the metavariables with new bits of tree themselves capped by metavariables.
The `result : expr` is the root of this tree. The `goals` are a list of the metavariables that we wish to grow next.
The `tactic` monad is a monad that can access the tactic state and use it's various methods to successively grow this tree.

Now in the `begin` block we specify a sequence of tactics, which are themselves composed of more tactics and so on until you reach the _fundamental_ tactics. These are the tactics which control some C++ code that actually performs the manipulations on `tactic_state`. The fundamental tactics have been chosen in such a way that it _should_ be impossible to make the `result` be an invalid term. Although I believe there are ways of making invalid `result`s ([TODO] this is what happens when you get the `result of a buggy tactic` error?). It's not a showstopper if you make an invalid expression though, because it will be caught by the kernel.

After all of the tactics have been applied, and assuming none of them failed. You will now have a new tactic state. At the `end` of the block, Lean will do the following checks

- Is the goal list empty? If not error with "tactic failed, there are unsolved goals".
- Does the `result`, depend on any unassigned metavariables? If so then error with "tactic failed, result contains meta-variables".
- Does the `result` typecheck and have no unbound variables? ([TODO] I suspect this is more complicated, since some `result` terms are huge and involve macros, so there is some wizardry going on where Lean is returning promises to make the proof term and so on)
- [TODO] any more?

If it passes these then Lean is satisfied and you have constructed a valid proof term for your lemma.
If your proof contains `sorry`, then Lean will give you a disapproving warning. You can almost hear Lean sighing: lamenting your inadequacy.

## Fundamental tactics which don't use fancy matching and reduction.

The best thing to do to learn about these is to read `library/init/meta/tactic.lean` and look at the lines beginning with "`meta constant`". Most of them have documentation, but some of them don't tell you much. So I hope to fill in the gaps with this document.

### Tactics for manipulating the environment
- `add_decl : declaration → tactic unit` adds a new declaration to the environment. Note how it _mutates_ the environment: it doesn't return a new environment with the declaration added.
- `env` gets the environment.
- `set_env`
- `doc_string` and `add_doc_string`. Change doc strings. This is super cool because it means you can programmatically generate docstrings!
- `module_doc_strings : tactic (list (option name × string))` looks in the current module and returns all of the names and docstrings of the declarations in it. [TODO] what _exactly_ is a module?
- `add_aux_decl` use this to add a new declaration to the environment where it also figures out what local_constants the declaration depends on and adds those as implicit arguments. [TODO] How is it deciding what to make implicit/ explicit?
- `open_namespaces` returns the list of currently open namespaces.
- `decl_name : tactic name` The name of the declaration currently being elaborated.

[TODO] it's kind of clear what all of the below do but the details of the arguments are not documented.
```lean
/-- Set attribute `attr_name` for constant `c_name` with the given priority. If the priority is none, then use default -/
meta constant set_basic_attribute (attr_name : name) (c_name : name) (persistent := ff) (prio : option nat := none) : tactic unit
/-- `unset_attribute attr_name c_name` -/
meta constant unset_attribute : name → name → tactic unit
/-- `has_attribute attr_name c_name` succeeds if the declaration `decl_name` has the attribute `attr_name`. The result is the priority. -/
meta constant has_attribute : name → name → tactic nat
```

### [TODO] I still have no idea what these ones do:

- `save_type_info`
- `save_info_thunk`
- `kdepends_on`
- `kabstract`
- `unfreeze_local_instances`
- `frozen_local_instances`
- `subst_core`

### Assorted tactics for figuring out what the state is doing.

- `get_local : name → tactic expr`. Lookup the provided `name` in the local context and return the corresponding `local_const` expression.
- `resolve_name : name → pexpr`. Resolve a name using the current local context, environment, aliases, etc.
- `result : tactic expr`. Gets the result of the tactic state.
- `target : tactic expr`. Take the first goal in the goal list and look up the type of the metavariable. 
- `local_context : tactic (list expr)`. Dump the local context into a list. The expressions in the list are all `local_const`s.
- `get_goals : tactic (list expr)`. Dump the list of metavariables which are goals right now.
- [TODO] more to come.

### Assorted tactics for inspecting and manipulating expressions

A lot of the time you shouldn't use the `expr`-making equipment in the `expr` namespace, but instead use the ones found in `tactic`. This is because judging whether an `expr` is valid depends on the context which only the tactic state can know about. 

- `infer_type : expr → tactic expr` figure out the type of the given expr using the kernel's typechecker.
- ``get_unused_name (n : name := `_x) (i : option nat := none) : tactic name`` returns `n` unless something already has name `n` in the context, in which case it returns `n_X` where `X` is the first natural number such that this name isn't taken. You can also explicitly pass a number using the `i` argument. `get_unused_name` will _only_ look for clashing names in the local context. So doing ``get_unused_name `x`` twice will not return `x` then `x_1`.
- `eval_expr : Π α : Type [reflected α], expr → tactic α` tries to typecheck the given `expr`, and if it's `α` then it returns `α`. So this tactic kind of does the same job as anti-quotations.  [TODO] what is the `reflected α` typeclass doing? I don't understand
- `mk_app` and friends. `mk_app fn args transparency : tactic expr` looks at the type signature for `fn` and tries to match each of the `args` with an arg of `fn` and makes metavariables for the arguments it can't figure out. The exact mechanics of matching and transparency are discussed later.
- `to_expr : pexpr → tactic expr`. Basically tries to fill in  
- `type_check` Type check the given expr with respect to the current goal. [TODO] what does "with respect to the current goal" mean?

### fun_info

A lot of the time, you want to think of `app (app (app f x) y) z` as just `f` applied to arguments `[x,y,z]`.
`library/init/meta/fun_info.lean` is your friend here.

Suppose expression `f`'s type is a telescope of `pi`s (that is, of the form `Π x, Π y, ... r`).
Call the `x`, `y` etc __parameters__ and `r` the __result type__.
Then the `get_fun_info f` tactic will return a `fun_info` object, which has fields:
- `params` which is a list of `param_info` objects. One for each parameter in `f`'s type. A `param_info` is
    + `is_implicit` -- Is the parameter implicit (that is, in curly braces)?
    + `is_inst_implicit` -- Is the parameter an implicit typeclass instance argument?
    + `is_prop` -- is it a proposition? Ie: is it's type of type `Prop`?
    + `has_fwd_deps` -- Do later paramters or the result type depend on this parameter?
    + `back_deps : list nat` -- a list of references to the indices of the previous parameters that it depends on.
- `result_deps : list nat` -- the paramters that the result type depends on.

`get_fun_info` doesn't give the types of the parameter or the result type. You have to inspect these manually using pattern matching on the type.

[TODO] Does `get_fun_info` work when it has already been applied?

[TODO] I don't understand subsingletons. 
What is a subsingleton? It seems to be any type which is isomorphic to a member of Prop. Ie, it's either uninhabited or has one member.
- `get_subsingleton_info`
- `get_spec_prefix_size`
- `get_spec_subsingleton_info`

### Tactics for dealing with typeclasses.

- `is_class : expr → tactic bool` check if the given expr is a typeclass. I think this amounts to checking if it has the `class` attribute attached to it.
- `mk_instance : expr → tactic expr` tries to make an instance of the given typeclass by trying to find an instance in the current context.

### Tactics for printing stuff.

- `format_result`
- 
[TODO] the `format` type.

- [TODO] I can't figure out the difference between `format_result >>= trace`, `trace_result` and `do { r ← result, s ← read, return (format_expr s r) }`, even with the help of `format_result`s docstring. I want an example.

### `set_goals`

The `goal`s list is really just a list, so you can change it however you want in your tactic. There are some gotchas though:
- All of the metavariables you pass to `set_goals` which are assigned will be omitted (this is what the `cleanup` tactic does).
- If you do `set_goals []`, you don't magically prove the result. Instead you will get the message "tactic failed, result contains meta-variables".
- If you accidentally pass an `expr` to `set_goals` that isn't a metavariable, you will see the message "invalid set_goals tactic, expressions must be meta-variables that have been declared in the current tactic_state".
- The metavariable doesn't have to be present on the `result` tree to be set as a goal. Such a metavariable is said to be __dangling__.
- [TODO] does it instantiate the metavariables in the type of the metavariable?

### `intro_core`

The `intro_core : name → tactic expr` tactic is used to 'unwind' binders in goals.

You should already know intuitively what `intro_core` does. But here is the explicit routine for `intro_core n`:
- Look at the first metavariable `M` in `goals` (the main goal) and look up its `type : expr` in the metavariable context.
- If `type` has the form `pi _ e₁ e₂`, then:
  + add a fresh local constant declaration with name `n` (make a fresh unique_name `n'`) and type `e₁` to the context. 
  + Instantiate `e₂` with `local_const n n' e₁` to get `e₃`.
  + Make a fresh metavariable `M'` with type `e₃`. 
  + Assign `lam n e₁ M'` to `M`
  + Replace `M` by `M'` in `goals`.
  + Return the new `local_const`.
- Similarly when `type` has the form `let n e₁ e₃ e₂`, but this time set the local constant declaration for `n` to have `value := some e₂`.

That was quite longwinded but it shows that the tactic state is not magic. We can invent a shorthand for describing the above procedure which takes advantage of the fact that manipulating the tactic state should only be allowed to make valid expressions.
My shorthand for `intro_core n` is `?M ~~> λ n, ?M'`.
We can figure out what all of the types are because we know that the inference rule for Π-introduction.  In this shorthand I'm also going to be sloppy with quotations and antiquotations.

Some warnings:
- The argument `n` is the pretty name for the local constant. `intro_core` won't complain if you run it twice with the same name, but this can lead to confusing tactic states where two hypotheses appear to have the same name. So suppose we run `intro_core x` twice, my observations suggest that now when we use the name `x` in future tactics, it will assume you are referencing the most recently `intro`ed hypothesis. This is generally called __name clobbering__.
- `intro_core` will _only_ work when the main goal metavariable is a `pi` or a `elet` expression. So it won't work if the target type is eg `(λ x, Π y, _) (_)`. The `intro` tactic does some work beforehand to reduce expressions like this. I will talk more about reductions in the next section.

Here is an example:

```lean
open tactic
lemma my_lemma (p q r : Prop) : 
    (p → q → r) → (p → q) → p → q ∧ r := 
begin 
    intro_core `h₁,
    sorry
end
#print my_lemma
/- prints:
theorem my_lemma : ∀ (p q r : Prop), (p → q → r) → (p → q) → p → q ∧ r :=
λ (p q r : Prop) (h₁ : p → q → r), sorry
-/
```

We can also use `intron : nat → tactic unit` which just `intro_core` applied `n` times. `intron` will guess the names based on the name given in the binder. 
If the name is already taken in the local context then it will append `_1` (unless `..._1` is taken, in which case `..._2` etc).
Note that since `p → q` is sugar for `Π a : p, q`, intros will very commonly give you the name `a`, `a_1`, `a_2` etc which can make the names look a little tedious.

### `revert_lst`

`revert_lst : list expr → tactic nat` is the reverse of `intron`. It takes a local constant `c` and puts it back.
If there are other local constants that depend on `c`, these are also reverted. Because of this, the `nat` that is returned is the actual number of reverted local constants.

### `define_core` and `assert_core`

`define_core n e` does : `?M ~~> let n : e := ?N in ?M'`. That is, it fills in the goal with an `elet` expression and makes two new goals.
`assert_core n e` does : `?M ~~> (λ n : e, ?M) ?N`.

Example:
```lean
open tactic
lemma my_lemma_2 (p q : Prop) : (p → q) → p → p ∧ q := 
begin 
    intros h hp,
    (get_local `q >>= define_core `hq),
    /-Look at the goal state here-/
    sorry
end
```
```lean
2 goals
p q : Prop,
h : p → q,
hp : p
⊢ q

p q : Prop,
h : p → q,
hp : p
⊢ let hq : q := ?m_1 in p ∧ q
```

The first goal is for the metavariable inside the `let` binder, Lean has called it `?m_1`.
Lean will throw away lambdas and let bindings that are created by the tactics but whose resulting local constants are never used anywhere.
There are also variants `assertv_core` and `definev_core` which take an additional `value` argument which is used to fill the first goal.

### `exact`

`exact x` does: `?M ~~> x`. That is, just fill in the main goal once-and-for-all with the `expr` x. Let's solve our first goal in the example with `exact h₁ pp`. We didn't need to faff around with `get_local` or backticks this time because we are using the interactive mode version of `exact`.

### `clear`

`clear x` takes the local constant `x` and removes it from the local context. This is possibly the most underrated tactic, throwing away junk is one of the most important things you can do to keep your sanity when proving things.
`clear` will tell you off if you try to `clear` a local constant that other local constants and metavariables depend on. I don't think it cares about dangling metavariables though.

## Making metavariables directly

You can use `mk_mvar : expr → tactic expr` to make fresh metavariables. The parameter is the type.
There is no way to directly assign (ie. "fill in") metavariables with a tactic. Instead, you have to assign them by: 
- setting them as a goal and using tactics which operate on the goal such as `exact` and `apply`
- or getting them set as a result of unification, which is when a metavariable is set because a matcher wanted (eg) `f ?m` and `f 4` to be equal.

## Comparing Expressions: Reduction, Matching, Unifying and so on

We often need to take two `expr`s and check if they are 'the same'. We will write an "are they the same?" question as `s =?= t`.
But alas there are lots of ways to interpret `the same' and we need to use different interpretations in different circumstances.

- The most obvious measure of sameness is just to check that the `expr`s look _precisely_ the same: just go through the tree and recursively check that all of the arguments for the `expr` cases are equal. This is called __structural equality__.
- The next one is the same as the above but we forget about the `name` parameter on `expr`s which bind things. This is called __equality up to α-equivalence__. In Lean this is done automatically because of de-Bruijn indices so Lean calls this structural equality too.
- Our type theory CIC comes with a set of reduction rules -- stated below. Which are ways of transforming exprs. If two `expr`s are structurally equal up to performing reductions, we say the expressions are __definitionally equal__. Lean's kernel uses definitional equality to check if types etc are equal.
- Often the expressions we are matching will involve metavariables. Then if we find ourselves needing `?m =?= t` to be true, we can assign `t` to `?m` to force the terms to match. This is called __unification__. -- [TODO] sort out exactly what __unification constraints__ are?
- If you are only allowed to assign metavariables on the _left_ ([TODO] check this) hand side of the `=?=` then we call it __matching__. (In Lean, this is morally true but matching can also sometimes assign typeclass metavariables on the right, see the giant comment in `src/)
- Finally, it is worth mentioning the undecidable: "is there a sequence of rewrite rules that will make these terms equal?". The best book to read about this kind of 'sameness' is Nipkov's _Term Rewriting and All That_. [TODO] what is this kind of equality called? "rewrite equivalence" or something.

[TODO] What does Lean do for (undecidable) higher unification problems? It looks like in some special cases it actually has a go at doing it. Eg when guessing the motive for `rec`. I think this is discussed in the `Elaboration in Lean` paper.

[NOTE] Unification is a huge area of research so I am having some trouble deciding what to include in this doc. I am also finding it difficult to figure out exactly which unification algorithms Lean is using. Eg. It seems to be doing higher order unification in some special cases so I guess it's using something like Huet's algorithm to do this. There are also loads of settings that one can pass to the unifier which I don't understand (eg what exactly does the `approx` setting do in `apply_core`?)

### Reduction in Lean

Let's write out all of the fundamental reductions we have in type theory. We write 'equivalence' when we have a reduction which doesn't terminate. So for example we could perform α-equivalence forever.
- __α-equivalence__ is renaming bound variables. Thanks to de-Bruijn indices this is done automatically.
- __β-reduction__ is `(λ x : a, b) c ~~> b[x/c]`
- __δ-reduction__ is replacing a constant with it's definition.
- __ζ-reduction__ is reduction of `let` bindings: `let x : a := b in c ~~> c[x/b]`. Perform it on an expression with the `zeta` or `head_zeta` tactic.
- __η-equivalence__ is the rule that  `(λ x, f x)` can be reduced to `f`. Perform it with the `eta` or `head_eta` tactic. 
    You can also use the tactic `head_eta_expand` to do η-reduction backwards. Eg; `f` is converted to `(λ x, f x)`. If `f` isn't a function then it just returns `f`.
- __ι-reduction__ is reducing recursors on inductive datatypes: for example `nat.rec i r (succ n) ~~> r n (nat.rec i r n)` and `nat.rec i r 0 ~~> i`. Reducing any recursively defined function.
- __proof-irrelevance__ if `P : Prop` and `a b : P`, then `a` is equivalent to `b`.

Interestingly, ι-reduction and proof-irrelevance together make definitional equality undecidable. But only cases which we don't really care about are undecidable so it's ok. See section 3.7 of the [Lean Reference Manual](https://leanprover.github.io/reference/lean_reference.pdf).

You can get Lean to do a bit of these
- 

### What is WHNF?

'WHNF' stands for "weak head normal form". This basically means "apply the minimal amount of reductions so that the root of the `expr` can't be reduced further". Often this is less work than fully reducing the expression and often we only care what the root looks like anyway.
There is [a stack overflow answer](https://stackoverflow.com/questions/6872898/haskell-what-is-weak-head-normal-form) that explains WHNF well. Finding the WHNF is decidable but in general but can take arbitrarily long to compute.
You can put an expression in WHNF using the `whnf` tactic. You can see this used in the `intro` tactic.

### Transparency

[TODO] Asked about it on Zulip.

### Fundamental tactics for unifying and matching expressions

- `unify`
- `is_def_eq`
- [TODO]

### `mk_app` and friends.

The docstring is great for this one so I'm just going to paste it in.
> Helper tactic for creating simple applications where some arguments are inferred usingntype inference.
> Example, given
>   ```lean
>       rel.{l_1 l_2} : Pi (α : Type.{l_1}) (β : α -> Type.{l_2}), (Pi x : α, β x) -> (Pi x : α, β x) -> , Prop
>       nat     : Type
>       real    : Type
>       vec.{l} : Pi (α : Type l) (n : nat), Type.{l1}
>       f g     : Pi (n : nat), vec real n
>   ```
>   then
>   ```lean
>   mk_app_core semireducible "rel" [f, g]
>   ```
>   returns the application
>   ```lean
>   rel.{1 2} nat (fun n : nat, vec real n) f g
>   ```

There are a lot of variants of `mk_app` that are also included for efficiency on equational reasoning.

- `mk_mapp` -- explicitly state which arguments should be inferred.
- `mk_congr_arg` -- `eq.congr_arg : Π (f : α → β),  a₁ = a₂ → f a₁ = f a₂`
- `mk_congr_fun` -- `eq.congr_fun : (f = g) → Π (a : α), f a = g a `
- `mk_congr` -- `eq.congr : (f₁ = f₂) → (a₁ = a₂) → f₁ a₁ = f₂ a₂`
- `mk_eq_refl` -- `eq.refl : Π(a : α), a = a`
- `mk_eq_symm` -- `eq.symm : a = b → b = a`
- `mk_eq_trans` -- `eq.trans : a = b → b = c → a = c`
- `mk_eq_mp` -- `eq.mp : α = β → α → β`
- `mk_eq_mpr` -- `eq.mrp : α = β → β → α`

### `apply` and friends.

Here is what `apply_core fn` does:

- Get the type signature of `fn`. Unwind the `pi`s to get `fn : Π (a:A) (b:B) (c:C) ..., X → Y → Z(a,b,c. ...)`. That is, `fn`'s type is a telescope of `pi`s and I am using the convention that the return type `Z` depends on the bound variables `a,b,c` at the start of the alphabet but not on `X,Y`. `X`,`Y` might also depend on `a`,`b` and so on.
- For each argument `A,B` ... `X,Y`, make a fresh metavariable `?a,?b, ... ?x,?y`.
- Unify (that is, do definitional equality while assigning metavariables) the return type of `fn` with the main goal type `G`: `Z(?a,...) =?= G`. There are various settings which change exactly how the unification works to be discussed below. If unification fails, then `apply_core` fails too.
- Now that unification has succeeded, assign `fn ?a ?b ... ?x ?y` to the goal metavariable and add all of the new metavariables that weren't assigned by the unification as a goal.

 [TODO] what definitions are we allowed to expand? Does it put it in WHNF first?

We can also pass some options to `apply_core`.
The configuration structure is called `apply_cfg` and has the following fields:

- `(md := semireducible)` -- the transparency mode for the unifier to use (basically: how aggressively should it unfold definitions?).
- `(approx := tt)` -- [TODO] Something to do with how to fallback if higher order unification fails. Not sure.
- `(new_goals := new_goals.non_dep_first)` -- Decides which new metavariables for the arguments should be added as goals. See below definition of `new_goals`.
- `(instances     := tt)` -- synthesize unresolved `[...]` arguments using type class resolution.
- `(auto_param    := tt)` -- `apply` tries to synthesize unresolved `(h : p . tac_id)` arguments using tactic `tac_id`. It doesn't do anything in `apply_core`.
- `(opt_param     := tt)` -- `apply` tries to synthesize unresolved `(a : t := v)` arguments by setting them to `v`. It doesn't do anything in `apply_core`.
- `(unify         := tt)` -- if true then it will assign metavariables that appear in the goal.

`new_goals` is an inductive type over the following constructors:
- `non_dep_only` --  only set as goals the metavariables `?a`, `?b` etc. Not the `?x`, `?y` ones.
- `non_dep_first` -- change the ordering of the goals so that the non-dependent goals are first in the goal queue. The idea is that once you have solved the non_dep goals it is likely that the dependent goals will have been unified.
- `all` -- Turn all of the arguments in to goals in the order that they appeared in `fn`'s type.

[TODO] does the unifier treat implicit arguments differently?

### [TODO] simp and rewrite and so on

`simp` is a tactic written in C++ that applies lots of lemmas tagged with the `simp` attribute. [Kevin Buzzard wrote about this](https://github.com/leanprover/mathlib/blob/master/docs/extras/simp.md).

`rewrite` takes a proof of an equation as an argument and looks around trying to find a subexpression that matches with the LHS of the equation. 

[TODO] some questions:
- Is simp using a measure of term size?
- What tactics is using simp behind the scenes? 
- Is simp the thing that expands definitions or does it just apply lemmas tagged with `@[simp]`?
- Overall , I wonder whether `simp` could in principle be written as something in Lean. Is it just for perf reasons that it's in C++?
- What is the exact difference with `dsimp`?