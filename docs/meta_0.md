# How `meta` works. Part 0: Expressions

I am going to assume that readers are familiar with dependent type theory and proving things in Lean.
But not with how these things are implemented on an actual computer.
I will also assume that the reader is comfortable with functional programming concepts such as `monad`,  `functor`, `alternative` and `applicative`.
The reader should also be aware that I am a beginner to Lean, but not to the internals of theorem provers, so it is very likely that this docuement contains misleading errors.
Some of the text is copied from docstrings in the Lean library or from answers on Zulip. I would like to thank Mario Carneiro, Leo de Moura, Gabriel Ebner, Simon Hudon, Sebastian Ullrich, Kevin Buzzard, Rob Lewis and everyone else in the Lean community chat for helping me out.
Finally, I am trying to write this for a mathematician who wants to gain an understanding of what is going on under the hood rather than for pro type theorists. So I will make lots of simplifications and analogies that should really come braced with a page of caveats and footnotes. If you want to get nitpicky then you will just have to study actual textbooks, papers and source-code on the topic.

## What is a type theory?

Suppose we want come up with a new type theory `T`. This is composed of:

- A term structure -- things like "if `s` and `t` are terms, then `s $ t` is a term. So a term is just a tree full of variables and constants and binders and so on.
- A set of inference rules on typed terms -- "if `s : A -> B` and `t : A`, then `s $ t :  B`". These are often written as `(s : A -> B) (t : A) ⊢ (s $ t :  B)` or as
  ```
  s : A -> B
  t : A
  ----------
  s $ t : B
  ```
  Type theory papers are littered with pages and pages of these inference rules. They define what it means for a term to be well-typed. Mario has written a doc containing the [inference rules for Lean](https://github.com/digama0/lean-type-theory/releases/download/v0.21/main.pdf).
- Term reductions. These are some transformations that one can perform on terms to do computation.
  So for example we have β-reduction which says that `(λ x, T) $ y` reduces to `T` where all occurrences of `x` are substituted with `y`.
  Typically, the reductions are reduction of lambdas, let bindings and reduction of the `rec` functions on the various inductive types such as ℕ and `prod`. See the section on reduction rules in the next part.

Now we have specified the type theory, we need to write a computer program which will be able to construct elements of this type theory and perform reductions on them.
This is what Lean does for a version of type theory called the _Calculus of Inductive Constructions_ or _CIC_.

## What does it mean to be meta?

The idea of logic is to construct mathematical structures within which we can do mathematics.
In type theory, the structures are trees of terms which obey the given inference rules.

But in order to construct these objects, we need to do activities that are _outside_ the structure: deciding what type theory to use, writing the code that manipulates trees of terms, applying reductions to terms, parsing strings into terms, checking that the inference rules are being applied correctly and so on.
We call these __meta-level__ activities. Anything to do with the mathematics: proving a theorem, writing a definition, defining an inductive type ... is called __object-level__.

In most systems, the meta-level activities are done in a different language to the one that we use to do mathematics. In Isabelle, the meta-level language is ML and Scala. In Coq, it's OCAML. In AGDA it's Haskell. In Lean, most of the meta-level code is written in C++.

Now, the cool thing about Lean is that it exposes structures within the _object-level_ which can manipulate the _meta-level_.
So for example, there is an inductive type called `expr`, which just looks like any other inductive type. But if we write an _object-level_ function that manipulates `expr` in some way, then Lean can __reflect__ ([TODO] is this the right word?) this definition into a _meta-level_ function that can be used to prove things.

This means that we can write code within Lean that changes how Lean performs its meta-level activities.
Lean carefully restricts what you are allowed to do though, so you can't (in theory) change the meta-level activities enough to prove `false`!
Lean does this with trust levels. When you write some Lean code that is going to be reflected up to meta, you have to add the keyword `meta` to your definition. Once this happens, Lean no longer trusts that the code is sound. So you can't use your `meta` tagged object to construct objects which aren't tagged with `meta`.

The `meta` keyword in Lean is a bit of a misnomer - it is more accurate to call this "unsafe", because it enables a number of unsound mechanisms, and while it is useful for metaprogramming it is not exclusively used for this. Not all metaprogramming things are meta, and not all meta things are used in metaprogramming.

## Setting the stage

Here I will introduce the main meta-level constructs that Lean exposes to you from within the Lean language.

### universe level

To avoid paradoxes (think; "does the type of all types contain itself?"), we have an infinite hierarchy of type universes.
You can think of a universe level as just a natural number, but remember that these numbers are at the meta level. That means that the numbers are used to talk about things within Lean, rather than being an object of study itself. Here is the definition, given in `library/init/meta/level.lean` in the Lean codebase with my comments

```lean
meta inductive level
|zero : level                    -- The zeroth universe. This is also called `Prop`.
|succ : level → level           -- The successor of the given universe
|max  : level → level → level  -- The maximum of the given two universes
|imax : level → level → level  -- Same as `max`, except that `imax u zero` reduces to `zero`. This is used to make sure `Π x, t` is a proposition if `t` is too.
|param : name → level           -- A named parameter universe. Eg, at the beginning of a Lean file you would write
|mvar : name → level            -- A metavariable, to be explained later.
```

Universes can be thought of as a bookkeeping exercise to stop the paradoxes and Lean does a good job of hiding them in most circumstances.
Because of this, I will try my hardest to omit details about type universes for the rest of this document.

### environments, declarations and names

When we write a Lean document, Lean constructs an `environment` that contains all of the constants and definitions that we we have put in the document.
You can think of the environment as a giant sequence of things called `declaration`s.
Each `declaration` in an environment has a unique `name`.
A name is just a list of strings `string1.string2.string3 ...`. We use a list of strings because then we can have things like `namespaces`.

```lean
inductive name
| anonymous  : name                     -- the empty name
| mk_string  : string → name → name   -- append a string to the front of the name
| mk_numeral : unsigned → name → name -- append a number to the front of the name
```

```lean
meta inductive declaration
/- definition: name, list universe parameters, type, value, is_trusted -/
| defn : name → list name → expr → expr → reducibility_hints → bool → declaration
/- theorem: name, list universe parameters, type, value (remark: theorems are always trusted) -/
| thm  : name → list name → expr → task expr → declaration
/- constant assumption: name, list universe parameters, type, is_trusted -/
| cnst : name → list name → expr → bool → declaration
/- axiom : name → list universe parameters, type (remark: axioms are always trusted) -/
| ax   : name → list name → expr → declaration
```

When one writes `map succ [4,5,6,7]` in a new Lean file, it doesn't parse, because Lean can't find anything in the environment or context with the name `map` or `succ`. We have to give their full names `list.map nat.succ [4,5,6,7]`. Alternatively, we can add `open nat list` above, this tells Lean that if it can't find something called `x`, it should also try out `list.x` and `nat.x`. Lean is also clever and can usually disambiguate a name clash using their type information.

Environments also contain notation: infix operators, etc. I can't find any programmatic ways of getting or setting notation for the environment.
Declarations can also be tagged with things called `attributes`. These are bits of extra data that give hints about how these declarations should be treated by Lean and by your tactics.

### Getting `names` in Lean

We can use backticks `` ` `` to access names from Lean objects.

* `` `my.name`` is the way to refer to a name. It is essentially a form of string quoting; no checks are done besides parsing dots into namespaced names
* ``` ``some ``` does name resolution at parse time, so it expands to `` `option.some`` and will error if the given name doesn't exist

## Expressions

The Lean type `expr` is just an inductive datatype that you can look at like any other. Let me give a cut down version of the one given in `library/init/meta/expr.lean` where I throw away some details to add back in later.

```lean
/-- THIS IS NOT THE REAL DEFINITION, I'VE SIMPLIFIED IT! -/
meta inductive expr
| var   : nat → expr                          -- A bound de-Bruijn variable.
| sort  : level → expr                        -- A type universe.
| const : name → list level → expr           -- A reference to a declaration in the environment with universe arguments.
| app   : expr → expr → expr                 -- A function call.
| lam   : name → binder_info → expr → expr → expr         -- A lambda expression. `name` is the name of the variable. The first `expr` argument is the type of the variable. 
| pi    : name → binder_info → expr → expr → expr         -- A pi expression.
| elet  : name → expr → expr → expr → expr -- A let expression.
| ... some other stuff to be introduced later ...
```
I will talk about `binder_info` later.
We can represent any Lean term using the above definition. 
Multiple arguments are done using _partial application_: `f x y ~~> app (app f x) y`.

### de-Bruijn Indexes

Consider the following lambda expression ` (λ f x, f x x) (λ x y, x + y) 5`, we have to be very careful when we reduce this, because we get a clash in the  variable `x`.
To avoid variable name-clash carnage, `expr`s use a nifty trick called __de-Bruijn indexes__.
In de-Bruijn indexing, each variable bound by a `lam` or a `pi` is converted into a number `n`. 
The number says how many binders up the `expr` tree we should look to find the binder which binds this variable.
So our above example would become (putting wildcards `_` in the type arguments for now for brevity):
`app (app (lam "f" _ (lam "x" _ (app (app [1] [0]) [0]))) (lam "x" _ (lam "y" _ (app (app plus [1]) [0])))) five`
Now we don't need to rename variables when we perform β-reduction. We also really easily check if two `expr`s containing bound expressions are equal.

This is why the signature of the `var` case is `nat → expr` and not `name → expr`.
If in our `expr`, all `var`s are bound, we say that the `expr` is __closed__.
The process of replacing all instances of an unbound `var` with an `expr` is called __instantiation__.
Going the other way is called __abstraction__.

### Getting `expr`s in Lean.

As fun as it would be to type out `expr`s in terms of `var`, `lam`, etc and doing all of the de-Bruijn index bookkepping yourself,
Lean provides a syntax to quickly convert any Lean expression into an `expr`.

* `` `(my expr)`` constructs an expression at parse time, resolving what it can in the current (of the tactic) namespace
* ``` ``(my pexpr)``` constructs a pre-expression at parse time, resolving in the current (of the tactic) namespace
* ```` ```(my pexpr)```` constructs a pexpr, but defers resolution to run time (of the tactic), meaning that any references will be resolved in the namespace of the begin end block of the user, rather than the tactic itself

The process of taking a string of unicode characters and converting them into a Lean expression is called _elaboration_. I will come back to elaboration.

A shorthand for going from an `expr` `e` to an actual Lean object is to use `%%e`. This is called  an __anti-quotation__.

### Implicit arguments and `binder_info`

Lean supports some extra information about binders that lets us write more concise code.
The two main mechanisms that Lean uses are __implicit arguments__ and __typeclass instances__.

Each `lam` or `pi` binder comes with a `binder_info` argument. This can be set to
- `default` -- just a normal argument
- `implicit` -- an implicit argument (arguments in curly braces)
- `strict_implicit` -- [TODO] What is the difference between `implicit` and `strict_implicit`?
- `inst_implicit` -- An implicit typeclass instance. These are the things in the square brackets such as `[group G]`.
- `aux_decl` -- [TODO] I don't know what this one does.

## Constructing valid `expr`s

You may notice that it is possible to make lots of badly typed `expr`s.
For example, `lam "f" nat (app [0] [0])`. 

So just having an `expr` term tree is not enough to count as something that Lean can use to prove theorems.
Lean has to be able to show that the `expr` could have been built using the inference rules of CIC. We say that an `expr` with this property is __valid__.

Lean does this by running an `expr` through a __type-checker__. The type-checker takes an `expr` and recursively type-checks it's sub-`expr`s until eventually erroring or returning a new `expr` giving the type of the provided `expr`.
Type-checking is done by Lean's __kernel__. 
If there is a bug in the kernel, then you can make nonsense terms which type-check and the entire system will become useless. 
So it's important that the kernel is small so that it can be easily reviewed by lots of humans for bugs. 
The Lean kernel is about 6,000 lines of code and lives in `src/kernel`. 
So if you want to be _totally sure_ that Lean is correct you have to learn C++ and carefully read all of this.

Now, writing down `expr` trees is very time consuming, because you have to manually add all of the type arguments.
For example,
```lean
set_option pp.all true -- show all of the gory details.
#check (λ x , x + 2 )
/- outputs:
λ (x : nat), @has_add.add.{0} nat nat.has_add x (@bit0.{0} nat nat.has_add (@has_one.one.{0} nat nat.has_one))
-/
```

We don't want to have to write out all of that every single time, so we use an __elaborator__ to figure out what all of the implicit arguments and typeclass arguments are.

Briefly, we turn a string of text into a Lean expression by first parsing the text to get a __pre-expression__ (`pexpr` in Lean). Each implicit argument in the `pexpr` is a special __placeholder__ expression `_`. We then pass the `pexpr` to an elaborator which will try to fill in each of these placeholders with an expression. 

Similarly, when we make a proof using tactics, we use tactics to figure out all of the details of the `expr` representing the proof term.
Let's look at how Lean does this for tactics first. And then look at the elaborator.

Read on at Part 1! [TODO] link.