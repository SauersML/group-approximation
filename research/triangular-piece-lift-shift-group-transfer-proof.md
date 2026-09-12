---
rg: 2
id: triangular-piece-lift-shift-group-transfer-proof
kind: route
title: Each vanishing piece is a one-coset equation that survives in any group carrying the partial conjugations; a left inverse there contradicts direct finiteness
target: triangular-piece-lifts-need-non-directly-finite-shift-group
requires:
  - finite-subgroup-idempotent-ideals-admit-no-proper-group-shift
artifacts:
  - research/artifacts/triangular-lift-hnn-transfer-2026-09-12.md
---

Artifact Section 4: Lemma 4.1, Theorem 4.2 and Corollary 4.3.
- **Vanishing pieces transfer.** `X_ij = 0` gives `E_i ⊗ E_j = 0` over `F_2[D_ij]`, by injectivity on one double coset
  in `R^x`. The map `x ⊗ y |-> x[t_i^(-1) t_j]y` is well defined on that tensor product in `H`, so
  `E_i[t_i^(-1) t_j]E_j = 0` in `H`.
- **Left inverse in `H`.** `x = sum [t_i]E_i` has `(sum E_i[t_i^(-1)]) x = 1 + nilpotent`.
- **Contradiction.** Direct finiteness would make `x` invertible, hence `a` invertible, hence `s0` invertible in `R`.
- **Forests.**
  - A change of free basis along tree edges turns every relation into an HNN relation along one letter.
  - For finite `K`, `H_Z` is then the fundamental group of a finite graph of finite groups.
  - Such a group is virtually free (as for the shift theorem), so its group algebra is stably finite.
