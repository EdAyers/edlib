/- 
My wishlist for Lean.

# Notation.

- there should not be a `in` to finish a `let` expression.

- have, let and suffices should all support the equation compiler, arguments.

    ```lean
       have x : A ⊕ B → C
            |inl a := ...
            |inr b := ...
       
    ```

# Lean-messages window

It would be really cool if there was a two-way interactivity between the window and the page.
 - if I click on a constant, it unfolds it.
 - I can double click on a local_const to rename it.
 - if I click on an inductive term, it performs `cases` on it
 - if I click on an equation, it does `subst` on it.
 - If I click on a hypothesis it tries to apply it to the target.
 - There is an 'x' after all of the local constants that I can use to dismiss them

# Pretty mode

This is a pie in the sky feature: the idea is that you can write out a notebook using 'mathedit' 
and the proofs will be done behind the scenes for you. It will make really pretty notation like
squareroots, fractions etc. This will require a complete overhaul of the parser which I have thought
a lot about but have decided to shelve.

 -/
