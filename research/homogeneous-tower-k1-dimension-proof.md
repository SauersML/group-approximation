---
rg: 2
id: homogeneous-tower-k1-dimension-proof
kind: route
title: Detect the null-homotopy at a stable-range stage and destabilize blockwise
target: homogeneous-tower-k1-failure-needs-twice-rank-dimension
requires: [bundle-endomorphism-unitaries-stable-range]
artifacts:
  - research/artifacts/stw18-k1-route-constraint-map-2026-09-11.md
  - research/artifacts/stw59-unique-trace-and-matrix-stability-2026-09-05.md
---

Let `u in U(A)` have `[u] = 0` in `K_1(A)`, so `u ⊕ 1_n` is null-homotopic in
`U(M_(n+1)(A))` for some `n`.

1. Approximate `u` within distance one by the image of some `u_i in U(A_i)`.
   The principal logarithm joins them, so the image of `u_i ⊕ 1_n` is
   null-homotopic in the limit.
2. Null-homotopies in injective unital inductive limits are detected at a
   finite stage, by the disk-approximation argument of Section 4 of the stw59
   unique-trace artifact (collar extension plus polar decomposition, keeping
   the boundary exact). So `phi_(i,j)(u_i) ⊕ 1_n` is null-homotopic in
   `M_(n+1)(A_j)` for all large `j`.
3. Choose such a `j` at which every block is in the stable range.
4. In block `k` the component `v_k` satisfies: `v_k ⊕ 1_n` is null-homotopic
   in `U(Gamma End((n+1) E_(j,k)))`. The prerequisite makes every
   stabilization from `m E_(j,k)` to `(m+1) E_(j,k)` an isomorphism on
   `pi_0`, because `d_(j,k) + 1 <= 2 r_(j,k) <= 2 m r_(j,k)`. Hence `v_k` is
   null-homotopic.
5. So `phi_(i,j)(u_i)` lies in `U_0(A_j)`, and `u` lies in `U_0(A)`.

The full write-up is Proposition D of the linked constraint-map artifact.
Square.
