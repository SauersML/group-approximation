---
rg: 2
id: consistency-defect-is-state-dependent-distance-proof
kind: route
title: Polarization, then the effect inequality
target: consistency-defect-is-state-dependent-distance
requires: []
artifacts:
  - GroupApproximation/Sofic/ConsistencyDistance.lean
---

Direct establishment, machine-checked in
`GroupApproximation/Sofic/ConsistencyDistance.lean`.

**Polarization.**  Expanding `(A-B)(A-B)^H` and using
`tau(X^H) = conj(tau(X))` gives, for single matrices,

```text
||A - B||^2 = ||A||^2 + ||B||^2 - 2 Re tau(A B^H).           (P1)
```

Summing `(P1)` over outcomes turns `(CD1)` into

```text
d(A,B) = sum_a ||A_a||^2 + sum_a ||B_a||^2 - 2 match(A,B),   (P2)
```

with `match(A,B) = sum_a Re tau(A_a B_a^H)` the matching mass, which is
`hsNormSq_sub` and `sdDistSq_eq`.

**Projections.**  If `P^H = P` and `P P = P` then `||P||^2 = Re tau(P)`
directly from `(P1)`'s ingredients, so

```text
sum_a ||A_a||^2 = Re tau(sum_a A_a) = Re tau(A_tot),          (P3)
```

and likewise for `B`.  Substituting `(P3)` into `(P2)` and comparing with
`(CD2)` -- whose total-overlap term is `Re tau(A_tot B_tot^H)` -- gives `(CD3)`.
Note that `A_tot = B_tot = 1` is used only to identify the two total terms with
each other; the value of `tau(1)` never appears, which is why the empty model
needs no exclusion.

**Effects.**  For `(CD4)` the same computation needs `tau(E^2) <= tau(E)` in
place of the equality `(P3)`.  The proof is the identity

```text
E - E^2 = E (1-E) E + (1-E) E (1-E),                          (P4)
```

valid because `E` and `1-E` commute.  With `E` and `1-E` both positive
semidefinite and both Hermitian, the two summands of `(P4)` are congruences
`B^H C B` of positive semidefinite matrices, hence positive semidefinite; so
`E - E^2` is, and its trace is a nonnegative real.  No square root, no spectral
theorem and no functional calculus is needed, which is what keeps the lemma
free of the continuous functional calculus instance tower.

**Triangle.**  `d(A,C) <= 2 d(A,B) + 2 d(B,C)` is the outcomewise sum of
`||X + Y||^2 <= 2||X||^2 + 2||Y||^2` applied to `X = A_a - B_a`,
`Y = B_a - C_a`, which is `hsNormSq_add_le`.  The squared form is deliberate:
it needs no square roots and no norm instance on matrices, matching how
`hsNormSq` is used throughout `Sofic`.

**Classical instance.**  For `P^f_a = diagonal 1_{f = a}`, the product
`P^f_a (P^g_a)^H` is `diagonal 1_{f = a and g = a}`, whose trace counts the
points where both functions take the value `a`.  Summing over `a` counts the
points where `f` and `g` agree, and subtracting from `tau(1) = 1` gives `(CD5)`.
