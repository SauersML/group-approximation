---
rg: 2
id: halving-invariant-k0-states-proof
kind: route
title: Average a state along the halving map and take a Markov–Kakutani fixed point
target: twisted-leavitt-k0-states-can-be-chosen-halving-invariant
requires: []
artifacts:
  - research/artifacts/halving-invariant-k0-states-2026-09-12.md
---

Section 2 of the artifact.
- The halving monoid map `F` of census §7.2 extends to an order-preserving endomorphism `F_*` of
  `K_0(A)`, and `m·F(u) = u`.
- For a state `s`, `m · s o F_*` is again a state.
- States form a nonempty compact convex subset of `R^(K_0(A))`: pointwise conditions, bounded by the
  order unit `u`, compact by Tychonoff.
- The map `s -> m · s o F_*` is continuous and affine, so it has a fixed point (Markov–Kakutani;
  explicitly, any limit point of Cesàro means).
