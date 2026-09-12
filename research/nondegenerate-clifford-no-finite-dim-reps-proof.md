---
rg: 2
id: nondegenerate-clifford-no-finite-dim-reps-proof
kind: route
title: A minimal-support element of an ideal is reduced to a unit by conjugating with a separating monomial
target: nondegenerate-clifford-skew-rings-have-no-finite-dim-reps
requires: []
artifacts:
  - research/artifacts/clifford-skew-ring-matrix-lamp-wreath-2026-09-12.md
---

The proofs are Proposition 2.1 and Corollaries 2.2–2.3 of the artifact.

- **Simplicity.** Choose a nonzero element of the ideal with minimal support, and two support points
  `v0 != v1`.
  - Nondegeneracy gives `w` with `b(v0 + v1, w) = 1`.
  - `a - (-1)^b(v0,w) c_w a c_w^-1` removes `v0` and keeps `v1` with coefficient `2 lambda_(v1)`.
  - So the minimal element is a unit monomial, and the ideal is everything.
- **No finite-dimensional representations.** A unital map `C_S tensor L -> M_n(L)` would be injective, but
  the source is infinite-dimensional.
- **Targets.**
  - Group algebras have the augmentation.
  - Marked-site rings evaluate at infinity onto `k[A^j x H]` or `k[F semidirect H]`, then onto a finite
    group algebra.
