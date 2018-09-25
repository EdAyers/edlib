import .topology

open topology filter
universe u
class uniform_space (X : Type u) :=
(uni : filter (X × X))