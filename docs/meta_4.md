# How `meta` works. Part 4: Term Rewriting. #

<!--
[NOTE]
The basic plan with this section is to first give an abstract view of how the methods work and then also provide tables explaining what everything does.
I am not too bothered if Lean 4 massively changes things, it will still be mostly the same.

[NOTE] Keywords and key-constants
- [ ] E-matching
- [ ] simplifier
- [ ] congruence, congruence closure
- [ ] `rw` tactic
- [ ] `cc` tactic
- 

-->


## What is term rewriting?
[TODO]
<!-- 
Give some examples of where it is needed.
They are a series of techniques for not having to spell out a sequence of rewrites.
Give references of theory: handbook of automated reasoning, TRAAT.

Explain some of the basic terminology

- rewrite rule
- congruence relation
- substitution
 -->


## The simplifier

The __simplifier__ in Lean is a suite of algorithms for brute-forcing proofs about transitive, reflexive relations from a fixed set of facts about these relations.

### Simp-Lemmas

The simplifier is armed with a set of rewrite rules called the `simp_lemmas`. We can think of the simp-lemmas as just being a giant set. But under the hood this set is sorted.

Each simp-lemma has the following data:
- A pair of `expr`s `l ~> r`. The rb map is indexed by the name of `get_app_fn(l)`.
- An relation `~~`. Simp assumes it is transitive and reflexive.
- A proof that `l ~~ r`.
- A kind which can be `Refl`, `Simp` or `Congr`.
    + A `Simp` is the default kind.
    + A `Congr` means that the given lemma `l ~~ r` is true when some number of other relations hold. So for example;
        `(?x_1 ↔ ?x_2) (?x_4 = ?x_6) (?x_5 = ?x_7), ite ?x_1 ?x_4 ?x_5 = ite ?x_2 ?x_6 ?x_7`.
    + [TODO] A `Refl` is the same as `Simp` except the proof is `rfl`. And therefore `l` is definitionally equal to `r`
- A list of the metavariables that the proof and `l` and `r` depend on.
- A priority number

You can list the default set in Lean with the command [TODO].
You can make your own sets of simp-lemmas using [TODO].

### What the simplifier does with simp-lemmas

<!-- [TODO] I'm going to just have to read the Lean C++ to understand exactly what it does.
In this section I want to focus more on how you can use the simplifier as an engine to traverse terms.
Eg, I would really like to use the simplifier to expand the definition of a recursively defined function and figure out the order in which induction should be applied.

 -->
- `simp_lemmas.rewrite`
- `simp_lemmas.drewrite`
- `simplify`


## Rewrite

## E-Matching and congruence closure.

<!-- [TODO]

- How E-matching works in general. Read up in TRWAAT and HAR, Bohua also covers it well. Leo's paper 'efficient E-matching' does a good job.
- What is SMT?
- Lean is more complicated because of ITT and `eq` vs `heq` etc.
- The important thing to stress is that they are not magic.

 -->

