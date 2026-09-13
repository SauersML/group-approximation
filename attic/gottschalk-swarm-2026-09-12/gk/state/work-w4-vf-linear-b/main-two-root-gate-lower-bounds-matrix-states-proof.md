---
rg: 2
id: two-root-gate-lower-bounds-matrix-states-proof
kind: route
title: Push-through makes matrix-state null quotients weakly finite, and the ring-algebra gate and the minor-only lower bounds then run on matrix states
target: two-root-gate-lower-bounds-hold-for-matrix-states
requires:
  - weakly-finite-leavitt-representations-killing-defect-are-trivial
  - sylvester-rank-functions-iff-no-triangular-certificate
  - odd-leavitt-unit-groups-mod-scalars-are-fp-simple
  - leavitt-gl-equals-el-and-perfect-unit-group
artifacts:
  - research/artifacts/two-root-certificates-separate-2026-09-12.md
---

Artifact Sections 1 and 2.
- **Census (Section 1).** [TRI] Theorem A and D.2, [RR] Propositions 6, 8 and Corollary 9, push-through, and
  the counting step of the rank gate contain no triangular step.
- **Lemma 2.1.** Push-through gives `n + d(I - YX) = d(I - XY) + n`, so the null quotient is weakly finite.
- **Theorem 2.2.** Apply `weakly-finite-leavitt-representations-killing-defect-are-trivial` in the null
  quotient.
- **Theorem 2.3.** Rerun the lower-bound proofs of the characteristic-three artifact. They use minors,
  additivity, subadditivity, commuting idempotent splits, conjugation and compactness only. Nonemptiness is
  item 2 of `sylvester-rank-functions-iff-no-triangular-certificate`.
