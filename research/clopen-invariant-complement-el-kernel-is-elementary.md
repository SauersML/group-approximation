---
rg: 2
id: clopen-invariant-complement-el-kernel-is-elementary
kind: claim
title: If the complement of a closed invariant Y is a union of clopen invariant sets, the kernel of EL_n(R_X) → EL_n(R_Y) is E_n(I_Y)
distinct_from:
  restriction-kernel-relative-elementary-off-minimal-sets: that controls kernels through bounded visit chains; this splits off clopen invariant pieces as direct factors and allows infinitely many minimal subsets accumulating on Y
artifacts:
  - research/artifacts/sk-k2-recurrent-2026-09-13.md
---

**ESTABLISHED (unreviewed)** via `clopen-invariant-complement-el-kernel-proof`.

Let X ⊆ A^Z be a subshift, Y ⊆ X closed invariant and n ≥ 2. If X∖Y is a union of clopen invariant subsets of X, then ker(EL_n(R_X) → EL_n(R_Y)) = E_n(I_Y).

Example: α_k → α irrational and X = X_α ∪ ⋃_k X_{α_k}. Each X_{α_k} is clopen, because the others accumulate only on X_α. The minimal subsets outside Y = X_α accumulate on Y.
