---
rg: 2
id: fpbs-relative-susceptibility-tube-excursion-bound-proof
kind: route
title: Exponential decay inside the tube and BK at the first exit vertex
target: fpbs-relative-susceptibility-tube-excursion-bound
requires: []
artifacts:
  - research/artifacts/fpbs/docs/fibre-summed-hyperbolic-quotient-criterion.md
---

Lemma 4.1 of the artifact.

1. **Tube term.** `T_r` is a finite union of `H`-cosets, and `H` acts on it with
   finitely many orbits. With coarse coordinate `n(x)` from `x = s(q) z^n`,
   edges change `n` by at most `L`, and at most `M_r` edges cross each level.
   Crossings of levels `2L` apart are independent, and each level is blocked
   with probability at least `(1-p)^(M_r)`. So
   `P(o <-> z^n inside T_r) <= (1-(1-p)^(M_r))^(floor(|n|/2L))`, and
   `C_r(p) < infinity`.
2. **Excursion term.** Suppose an open simple path from `o` to `z^n` leaves
   `T_r`. Its first vertex outside `T_r` projects to `S_Q(r+1)`, since each
   generator moves the quotient by at most one step. Splitting at that vertex
   `v` gives disjoint occurrence of `o <-> v` and `v <-> z^n`.
3. **Summation.** BK and summation over `v` and `n` give
   `sum_(|q|=r+1) sigma_p(q) sigma_p(q^(-1))`. This uses normality and
   `sigma_p(q^(-1)) = sigma_p(q)`.
