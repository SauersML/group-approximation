---
rg: 2
id: binary-power-witness-from-power-residue-donor-types
kind: route
title: Reach a power-residue donor-covering type, then split active symbols into phases until the alphabet size is a power of two
target: some-nonsurjunctive-group-gives-a-binary-power-one
requires:
  - strict-automata-reach-power-residue-donor-types
  - donor-covering-types-give-nonsurjunctive-size-progressions
---

1. Let `NS_all ≠ ∅`. By the first prerequisite some group `G` carries a strict donor-covering automaton of a
   power-residue type `(z, b)`, so `z + bt = 2^j` for some `t >= 1`.
2. Item 1 of the second prerequisite gives a strict automaton on `G` over `z + bt = 2^j` symbols. Since
   `z + bt >= z + b >= 2`, `j >= 1`, and `2^j ∈ NS(G) ⊆ NS_all`.

The first prerequisite is open. It asks less than `strict-automata-reduce-to-two-rest-donor-covering-ones`, which
feeds binary descent through `G × C_p`: every type `(2, b)` with `4 ∤ b` is power-residue, and so are types such as
`(3, 5)`, `(5, 3)` and `(z, 1)`, which that route cannot use.
