/- Defining with mutual inductive datatypes is also a pain -/

universes u v

inductive bnode (K : Type u) (A : Type v) : ℕ → Type max u v 
|Leaf {} : bnode 0
|Bk {n} (l : node n) (v : K×A) (r : node n): bnode (nat.succ n)
with node  : ℕ → Type max u v
|Bk {n} : bnode n → node n
|Rd {n} : rnode n → node n
with rnode : ℕ → Type max u v
|Rd {n} (l : bnode n) (v : K×A) (r : bnode n) : rnode n