---
rg: 2
id: linear-soficity-pi2-upper-bound-proof
kind: route
title: Rank metric is bi-invariant and subadditive, so the permutation argument transfers verbatim
target: linear-soficity-recognition-has-a-pi2-upper-bound
requires:
  - sofic-recognition-has-a-pi2-upper-bound
---

The normalized rank distance `rho(A, B) = rank(A - B)/n` on `GL_n(F)` is
a metric, bi-invariant (`rank(CAD - CBD) = rank(A - B)` for invertible
`C, D`), and satisfies `rho(A, 1) = rho(A^-1, 1)`.  These are the only
properties of the Hamming distance used in
[[sofic-recognition-has-a-pi2-upper-bound-proof]]: the forward direction
bounds the defect of a word by its length times the model accuracy through
right-invariance, and the backward direction converts a relator defect
`<= 1/k` into a defect `<= A/k` on every trivial word of area `<= A` by
conjugation invariance and subadditivity, then reads separation from the
listed nontrivial words through left-invariance.  With the separation
threshold `delta` fixed on both sides no amplification is needed (for the
`1 - eps` formulation one uses Arzhantseva--Paunescu's `1/4`
normalization).  Hence (LS1).

Decidability of the certificate: `n` and the finitely many matrices range
over an enumerable set (entries in a computable field), and `rank(A - B)`
is computed exactly by Gaussian elimination in `F`; comparison with `1/k`
and `delta` is a comparison of rationals.  So the second disjunct is an
existential over a decidable predicate, and (LS1) is `Pi^0_2`.

Heredity and locality are immediate from the definition (a model of a
finite subset of a subgroup is a model in the group and conversely), and
`delta`-linear soficity holds for sofic groups via permutation matrices,
since `rank(P_sigma - P_tau) >= (number of moved points)/2`... more
precisely `rank(P_sigma - 1)` equals the number of points moved by
`sigma` minus the number of nontrivial cycles, which is at least half the
number of moved points, giving separation `>= (1 - eps)/2 >= 1/4`.  So the
hypotheses of the second-level Rice theorem hold, and the dichotomy
follows exactly as for hyperlinearity in
[[approximation-property-recognition-dichotomy]].
