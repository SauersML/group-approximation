---
rg: 2
id: jacobson-shift-permutation-rounding-gap-proof
kind: route
title: Round monomial permutations and use the exact head commutator to exclude near-monomial models
target: jacobson-shift-monomial-models-have-a-uniform-gap
requires:
  - jacobson-shift-exact-representations-kill-head
  - jacobson-shift-gap-characterizes-mark-collapse
artifacts:
  - research/artifacts/jacobson-shift-exact-collapse-and-monomial-gap-2026-09-08.md
---

Monomial matrices with different permutations are at norm distance at
least `sqrt(2)`. At common approximation distance `a'`, finite table
errors are at most `3a'`, overlap errors at most `2a'`, and stable
intertwining errors at most `4a'`. The three mixed relators have
lengths `6,6,4` when individual finite-packet elements are letters.

For the middle bound, `c_P,k_P` belong to `Z`, so their commutator
word with `h` is the actual element `u in C`. With `z=a_Q r_P in B`,
the mixed word is `(u h) z (h u^-1 h) z^-1 h z`, with three
`C` letters alternating with three `B` letters. Thus
`delta+6a'<sqrt(2)` makes every relation exact in the permutation
quotient. The first prerequisite kills its head. The head approximants
are diagonal, so the exact commutator identity for `w` gives
`||rho_B(w)-I||<=4a'<2`, contradicting a retained involution.

Sections 4--5 of the artifact justify all identifications and passage
to the infimum over approximants and common bases.
