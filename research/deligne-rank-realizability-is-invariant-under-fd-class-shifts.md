---
rg: 2
id: deligne-rank-realizability-is-invariant-under-fd-class-shifts
kind: claim
title: Rank realizability of a multiplier of Sp4(Z) is unchanged by classes realized exactly in finite dimension
distinct_from:
  deligne-cover-linear-soficity-is-rank-projective-approximation: that proves the equivalence with linear soficity and the symmetry between the two sectors; this shifts the multiplier by any class realized by an exact finite-dimensional projective representation, with the same defect.
artifacts:
  - research/artifacts/deligne-rank-projective-rigidity-2026-09-12.md
---

Let `Gamma = Sp_4(Z)`, `p` a prime, and `beta` a normalized 2-cocycle of `Gamma` realized by an exact
finite-dimensional projective representation over an algebraically closed field of characteristic `p`. Suppose
a cocycle `alpha'` has rank-approximate projective representations in characteristic `p`. Then so do
`alpha' beta`, `alpha' beta^(-1)`, and every cohomologous cocycle `alpha' . delta(lambda)`.

So rank realizability of the Deligne multiplier depends only on its class modulo the classes realized exactly in
finite dimension. Perturbing exact Weil or theta representations of congruence quotients only shifts the target
class by such a class and does not change the problem.

**ESTABLISHED 2026-09-12** by `deligne-rank-fd-class-shift-proof` (artifact Proposition 2.2).
Verification requested from w4-vf-linear-b.
