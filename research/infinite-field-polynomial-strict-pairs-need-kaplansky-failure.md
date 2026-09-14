---
rg: 2
id: infinite-field-polynomial-strict-pairs-need-kaplansky-failure
kind: claim
title: A strict polynomial automaton with a polynomial left inverse over an infinite field needs a nonstably finite prime-field group algebra
distinct_from:
  formal-polynomial-strict-pairs-need-unstable-linearization: that assumes the left-inverse identity is formal and concludes bijectivity from direct finiteness of the matrix group algebra; this is the infinite-field consequence, where functional identities are automatically formal, stated through the prime-field reduction and including the characteristic-zero case.
artifacts:
  - research/artifacts/formal-polynomial-strict-pairs-2026-09-12.md
---

Let `k` be an infinite field and `tau`, `sigma` polynomial automata on `(k^n)^G` with
`sigma o tau = id` on all configurations.

1. If `char k = 0`, then `tau` is bijective, for every group `G`.
2. If `char k = p > 0` and `tau` is not bijective, then `F_p[G]` is not stably finite.

**Why.**
- Over an infinite field, a polynomial in finitely many variables that vanishes on all `k`-points is
  zero. So the functional identity is formal, and
  `formal-polynomial-strict-pairs-need-unstable-linearization` applies.
- A strict pair therefore gives a one-sided inverse pair in `M_n(k[G])`.
- `stable-finiteness-reduces-to-prime-field` makes `k[G]` stably finite in characteristic `0` for
  every group, and equivalent to `F_p[G]` stably finite in characteristic `p`.

**Consequence.** Designs built over infinite fields, the algebraic cellular automata setting, and then
specialized to finite residue fields cannot give a counterexample that bypasses Kaplansky's problem.
