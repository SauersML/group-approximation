---
rg: 2
id: stw77-counterexamples-reflect-to-separable-codomains
kind: claim
title: Every LXXVII counterexample has a separable codomain witness
distinct_from:
  stw77-hypotheses-and-stability-descend-to-quotients: that passes to a chosen quotient of the codomain; this theorem reflects all data to a separable subalgebra of an arbitrary codomain.
artifacts:
  - research/artifacts/stw77-map-oinfty-audit-2026-08-30.md
---

Suppose a unital map `phi:A->B` is a counterexample to Problem LXXVII:
`A` is separable and exact, `phi` has finite nuclear dimension, every
nonzero positive element of `phi(A)` is properly infinite in `B`, but `phi`
is not O-infinity-stable.  Then there is a separable unital C-star
subalgebra

```text
phi(A) subset B_0 subset B
```

such that the corestriction `phi_0:A->B_0` has the same four properties.
Moreover,

```text
dim_nuc(phi_0) <= dim_nuc(phi).
kappa_(phi_0)(F) >= kappa_phi(F) > 0
```

for some finite subset `F` of `A`, where `kappa` is the central-isometry
defect from the exact reformulation of O-infinity stability.  Thus the
failure of stability is retained with a finite quantitative witness, not
merely by an abstract sequence-algebra inclusion.

Consequently the arbitrary size of the codomain creates no separate
frontier in Problem LXXVII: a counterexample exists if and only if one with
both domain and codomain separable exists.
