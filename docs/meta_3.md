
# How `meta` works. Part 2: Elaboration

THIS SECTION IS STILL A WORK IN PROGRESS AND SO IS INCOHERENT.

Now that we have seen how tactics work. We can discuss elaboration. Recall that elaboration is the process of filling in all of the implicit arguments and typeclass instances that the user didn't want to write down.

-----------
[INFO] End of draft and start of ideas board.

# [TODO] Some general questions to sort out

- `subst_core` ?? apply to what?
- Does `mk_app` make metavariables?
- `unfreeze_local_instances` ??
- `get_tag` and `set_tag`. You can tag goals with names.
- if I have a goal with mvar M and M gets assigned, does the goal automatically disappear?
- I want to be able to 'rewind' mvar assignments like the C++ code is allowed to do with temporary metavariables. Are there built in mechanisms for this or do I have to track which mvars I want to temp assign myself?
- what is the 'equation compiler'?
- coercions
- what is the point of `options` in `tactic_state`? Where is it used? If I add my own options will they persist across different tactic_states?  

Important C++ files.
- `expr.cpp/h`
- `type_checker.cpp/h`
- `type_context`


[TODO] binder_info
[TODO] meta.format


# Elaboration

When you write down a string of characters such as `λ x, x + 3`, Lean turns this into a _valid_ `expr` through two stages:

1. __Parse__ the string into something called a __pre-expression__ or `pexpr`. Or fail if you typed in gobbledygook.
2. __Elaborate__ the `pexpr` into a valid `expr`. Or fail if it couldn't figure out what inference rules to use.

This is where `tactics` come in.

Elaboration is a special tactic built in to Lean that is used to turn strings of Lean code into `expr`s.



In order for an `expr` to be accepted by Lean, it has to be __elaborated__.
This essentially means that it has checked that it is possible to build the expression using the available inference rules.
Note how elaboration is also the process that occurs when you check a proof.
Elaboration is also the process of guessing what `expr`s fill 'holes' in the proof.
Consider the Lean code `#check λ x, x + 3`. If we inspect this in Lean, it will say it has the type `ℕ -> ℕ`. 
This was discovered using elaboration.

The best place to learn the gory details of Lean's elaborator is in the paper [Elaboration in Dependent Type Theory](https://arxiv.org/pdf/1505.04324.pdf) by four wise men.

## What happens when you run `#check`

I will likely get some details wrong here, but I think this is right enough to illustrate the process.

So you type the line `#check λ x, x`. What happens?
Firstly, a parser kicks in and turns the sequence of symbols you plonked on the page into a parse tree. 
The details of how the parsing works depend on what `notation` has been defined in the current environment, but it is just a straightforward conversion to a tree.
This structure is stored as something called a `pexpr` which stands for _pre-expression_.
So `λ x, x + 1` will be converted into a `pexpr` like `lam "x" _ (app (has_add.add [0]) has_one.one)`.
Notice how the parser has looked at `+` and figured out that in `library/init/core.lean`, the `+` symbol actually means `has_add.add`, similarly, `1 ~~> has_one.one`.
You can think of a pre-expression as an expression where there are lots of __placeholders__ that need to be filled in. These placeholders are implicit arguments, implicit typeclass instances and omitted types. 

The elaborator's job is to fill in these holes and also check that the expression can be built from the inference rules of the type theory. It does this by opening something like a tactic state (it's actually a different C++ class but it does roughly the same thing) and filling up the metavariable context with fresh metavariables, one for each placeholder in the pre-expression. The elaborator's job is now to __synthesize__ the `expr`s that the user intended them to be filled by. So you can kind of think of the elaborator as a super-awesome tactic for figuring out all of those boring implicit arguments.
There is a good paper about how it works called [Elaboration in Dependent Type Theory](??) that goes through all of the details of how these terms are synthesized, so I will leave it at that.

# Expression Macros 

- Macros are basically "promises" to build an expr by some C++ code, you can't build them in Lean.
- You can unfold a macro and force it to evaluate.
- They are used for `sorry`, meta-recursive calls, builtin projections.
- They are also used as ephemeral structures inside certain specialised tactics.

An example of a __meta-recursive call__:

```lean
meta def rec := rec
meta def rec : nat -> nat | x := rec (x + 1)
```

meta-recursive calls are not compiled to recursors like the non-meta versions. But instead to a promise macro in Lean which will actually do the computation.

Here is an example of a __builtin projection__:
```lean
structure foo := (mynat : ℕ)
#print foo.mynat

-- @[reducible]
-- def foo.mynat : foo → ℕ :=
-- λ (c : foo), [foo.mynat c]
```
The thing in brackets is a macro.

## pexpr

A `pexpr` is the parse tree of a given piece of lean text, so it still needs to be elaborated and have the implicit arguments put in and so forth.

`text --parse-> pexpr --elaborate-> expr`


## Reduction vs Evaluation

TODO 

# On with the show!

Supposing we have an `environment` full of terms and so on. We now want to get Lean to prove some new lemma `P`.
So we type `lemma asdf : P := `. What happens to the state of Lean? Firstly, it checks that `P` is a valid expression (eg doesn't have lots of unbound vars etc).

## Elaboration

TODO - it's important to realise that the elaborator is doing the same thing as a tactic. It's just that now the tactic is guided by the structure of the `pexpr`. In Lean 3 we are not given any say over the motions of the sacred elaborator, but this will change in Lean 4.

As far as I can tell. What happens is: The parser generates a `pexpr` and this is fed into the elaborator. The elaborator opens a new tactic_state and sets a pair of goals: `?α`, the type. And `?m`, the actual expression. We then build up the term slowly by looking at the pexpr and using `intro_core` and `mk_app_core` repeatedly and adding new metavariables for any implicit arguments. At the end we complete the task and have a proper expression.
I think that once you have an `expr` it becomes trivial to check the type so you can just use a different algo at that point.  

## A minimal set of tactics

A tactic is a State Result monad with some extra constructors bestowed on it by C++. All things of the below type are automatically tactics.
`tactic X := tactic_state -> (succ of tactic_state * X) + (fail of diagnostics * tactic_state)`
So this means that we can put an `alternative` structure on `tactic` and do that kind of stuff.

__`tactic_state`__ is a magic type. Here are the things you can do to it
- `env` -- gets the current environment
- `get/set_options` -- lets you mutate `options` which is basically just a dictionary with keys in name `name` and items being bools, nats or strings.
- `format_expr` -- TODO I think this is a fancy printer that formats in a way that respects the current goal. I don't get it.


## Datatypes for doing meta things

If you want to do any automation, it is likely that you will want to be able to store tables and sets of `exprs` and `names`.

The Lean core library has `rbtree` and `rbset`, but these seem to just be proofs of concept at the moment rather than things to use. For example, `rbtree` doesn't have an `erase` method!

But don't worry, because there is a namespace called `native` that you should look through.

- `rb_tree` a native C++ implementation of RB trees.
- `rb_set` 

## Caching data in the environment

If you are writing heavy duty tactics. You might want to to store a large cache of intermediate data.
You do this by adding it to the environment.

[TODO] `simp_lemmas`
[TODO] "you can cache data in special types inside user attributes as well.

>  I'm referring to the `cache_ty` and `param_ty` in `user_attribute`, 
> but it's not really a solution - `param_ty` has to be reflectable 
> (so it is probably just stored as an `expr`) and `cache_ty` needs to be 
> pure-functionally created from the list of all defs with the attribute 
> in the environment (so it can only depend on things that are ultimately `expr`s). 
> Still that cache has some promise.
>I'm not positive this is actually working the way you would want, but here's the general idea:
```
structure mydata := (n : nat)

@[user_attribute]
meta def mydata_attr : user_attribute (name_map mydata) unit :=
{ name := `mydata, descr := "stuff",
  cache_cfg := ⟨λ l, l.mfoldl (λ m n, do
    d ← get_decl n,
    v ← eval_expr mydata d.value,
    return (m.insert n v)) (name_map.mk _), []⟩ }

@[mydata] def X : mydata := ⟨500^2⟩

run_cmd do
  m ← mydata_attr.get_cache,
  v ← m.find ``X,
  trace v.n
```

# Using your own Type Theory: `normalizer_extension`s

There are lots of different type theories out there and type theorists spend a lot of time worrying that they are working in the right one. So it's important that Lean is able to support other type theories. Lean does this through normalizer extensions. You have to write them in C++ though. 
[TODO] Lean 2 had a HoTT mode. Is it technically possible to write a HoTT mode for Lean 3?

[FIXME] [TODO] [HACK] [BUG] [NOTE] [MARK]