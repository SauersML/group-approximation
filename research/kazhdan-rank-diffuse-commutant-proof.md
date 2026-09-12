---
rg: 2
id: kazhdan-rank-diffuse-commutant-proof
kind: route
title: Pass degree truncations of the finite-field representations to the rank ultraproduct
target: kazhdan-rank-ultraproducts-can-have-diffuse-commutants
requires:
  - elementary-group-property-t-over-free-algebras
artifacts:
  - research/artifacts/kazhdan-rank-rounding-counterexample-2026-09-12.md
---

## Why sufficient

`elementary-group-property-t-over-free-algebras` gives property (T) of `EL_3(F_2[t])`.
The rest is Section 4 of the artifact.

* **The chain.** `rank[pi_m (x) 1_3, rho_k(s)] <= 2 = o(3k)` for every generator, and the
  truncations are nested. So `p_beta = [pi_(m_k) (x) 1_3]`, with `m_k/k -> beta`, lie in
  the relative commutant.
* **Finite stage.** Irreducibility leaves only `0` and `1` as idempotents in each
  finite-stage commutant.
* **No atoms.** For representatives `V_k` of an invariant ideal, the subspaces
  `V_k n W_m` are almost invariant, with boundary at most `b(V_k) + 6`. Their dimension
  grows in steps of at most `3`, so every fraction of `dim V_k` is attained up to `O(1)`.
