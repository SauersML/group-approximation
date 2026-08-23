---
rg: 2
id: sl3-dyadic-building-action-soficity-forces-p-instability
kind: claim
title: Soficity of the dyadic SL3 vertex action forces genuinely noncorrectable permutation models
artifacts:
  - research/artifacts/sl3-dyadic-exact-action-firewall-2026-08-23.md
distinct_from:
  psl2-bruhat-tits-action-soficity-forces-p-instability: that is the rank-one analogue using Selberg property tau; here the integral stabilizer SL3(Z) itself is Kazhdan, and congruence co-density excludes every exact finite-action atlas for the rank-two building orbit.
  sl3-finite-building-quotients-forget-arithmetic-labels: that shows an unlabelled building quotient does not automatically descend the fixed arithmetic labels; this gives a quantitative impossibility theorem for supplying the labels from any exact finite action whatsoever.
  codense-kazhdan-coset-action-forces-permutation-outliers: that is the abstract Kazhdan/co-density theorem; this verifies both arithmetic hypotheses for SL3(Z) inside SL3(Z[1/2]) and identifies the type-zero building orbit.
---

Put

```text
A = SL_3(Z[1/2]),       C = SL_3(Z),       X = A/C.
```

The action `A action X`, equivalently the action on the type-zero vertices
of the `Q_2` affine Bruhat--Tits building, has a uniform orbit-atlas gap
against every genuine finite action of `A`.  Consequently,

```text
A action X sofic  ==>  A is not flexibly permutation-stable.       (SD1)
```

More precisely, fix `h in A\C` and a Kazhdan generating set of `C`.  A
Gao--Kunnawalkam Elayavalli--Patchell orbit approximation on the two-point
window `{C,h^(-1)C}` cannot be transferred, even after vanishing relative
padding, to an exact finite `A`-action with Hamming error tending to zero.

This eliminates both congruence and hypothetical non-congruence exact
finite-action constructions.  It does **not** decide whether the action is
sofic: a positive model would have to be an essentially noncorrectable
almost-action.  In particular, finite building quotients cannot be repaired
into the required coherent arithmetic labels by choosing a different family
of exact finite `A`-sets.

