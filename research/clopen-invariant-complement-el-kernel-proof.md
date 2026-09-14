---
rg: 2
id: clopen-invariant-complement-el-kernel-proof
kind: route
title: Clopen invariant pieces are central direct factors, so kernel elements are elementary over those factors
target: clopen-invariant-complement-el-kernel-is-elementary
requires: []
artifacts:
  - research/artifacts/sk-k2-recurrent-2026-09-13.md
---

Direct proof; `research/artifacts/sk-k2-recurrent-2026-09-13.md` §6.
1. For g ∈ ker π_Y, the coefficients of g − I and g^{-1} − I are supported in a clopen V ⊆ X∖Y. By compactness, finitely many clopen invariant U_i ⊆ X∖Y cover V.
2. U = ⋃U_i is clopen and invariant, so e_U commutes with u and with LC(X,F_2), hence is central. So g = (1−e_U)I_n + e_U g.
3. e_U g is the image of g under the ring homomorphism R_X → e_U R_X = R_U, so it lies in EL_n(R_U).
4. A factorization of e_U g into elementary matrices over R_U writes g as a product of e_ij(r) with r ∈ e_U R_X ⊆ I_Y. □
