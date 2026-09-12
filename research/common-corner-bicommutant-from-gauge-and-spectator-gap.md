---
rg: 2
id: common-corner-bicommutant-from-gauge-and-spectator-gap
kind: route
title: Combine common gauge alignment with a joint spectator gap
target: common-corner-mutual-bicommutant-extraction
requires:
  - one-cross-gram-moment-extracts-the-common-polar-gauge
  - two-mixed-pauli-commutators-lock-the-relative-reservoir-gauge
  - common-corner-word-pair-has-uniform-spectator-gap
---

Use the near-full cross-Gram moment before separating the child paths.  The
polar lemma gives one relative unitary `V` on their common exactified source
corner, and the two mixed Pauli words replace it by `U` in the required
relative reservoir commutant with total error

```text
sqrt(2Delta)+||[V,X]||_2+||[V,Z]||_2.
```

This aligns the two exactified named algebras on the same `o(1)` perturbation
of `P`.  Apply `(CSG1)` there.  At zero defect the joint commutant of the
commuting exact algebras `Atilde,Btilde` is scalar.  By the finite-dimensional
double-commutant theorem their join is therefore the full matrix corner.

It remains only the elementary exact implication from fullness to mutual
commutants.  A central projection of `Atilde` commutes with both algebras and
hence is scalar, so `Atilde` is a factor.  Conjugate it to
`M_r tensor I_m`.  Since `Btilde subset Atilde'=I_r tensor M_m` and their
join is full, `Btilde=I_r tensor M_m`; taking commutants gives
`Btilde'=Atilde`.  This proves all three clauses of `(CCMB1)`.

The uniform constant in `(CSG1)` is what makes the same argument stable
under the preceding `o(1)` perturbations.  Without that dependency,
`three-gauge-tests-leave-a-tensor-spectator` is an exact countermodel to this
route.
