---
rg: 2
id: odd-char-leavitt-unit-tensor-images-no-rank-function-proof
kind: route
title: Symmetrized roots give two orthogonal isometries, which null one cylinder tensor and then the identity
target: odd-char-leavitt-unit-tensor-images-have-no-rank-function
requires:
  - leavitt-gl-equals-el-and-perfect-unit-group
artifacts:
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
  - research/artifacts/diagonal-tensor-rank-functions-2026-09-12.md
---

Artifact Theorem 1.
1. **Symmetrized roots.** Inclusion–exclusion over `Δ_n(x_ij(Σ_(k in T) a_k))` isolates the symmetrized
   tensors `Sym_ij(a_1, ..., a_n)`, so they lie in `B_n`. This works because `e_ij(a) e_ij(b) = 0`.
2. **Isometries.** Take `2n` pairwise incomparable words and form `S_a = Sym_12(s_...)` and
   `T_a = (n!)^(-1) Sym_21(t_...)`.
   - They satisfy `T_0 S_0 = T_1 S_1 = e_22^(⊗n)` and `T_0 S_1 = T_1 S_0 = 0`.
   - Their ranges are orthogonal idempotents below `e_11^(⊗n)`.
   - This is the only step that needs `n!` invertible.
3. **One cylinder tensor is null.** Additivity gives `rk(e_11^(⊗n)) >= 2 rk(e_22^(⊗n))`. A signed
   permutation in `EL_3(F_p)` conjugates the two, so both have rank `0`.
4. **The identity is null.** Thompson's `V` conjugates `e_22^(⊗n)` to `p_A^(⊗n)` for every proper nonempty
   clopen `A`. Partition the Cantor set into `n + 1` clopen pieces and expand `1^(⊗n)`; by inclusion–exclusion
   it is a signed sum of `p_(A_T)^(⊗n)` over unions of at most `n` pieces. All of these are null, so
   `rk 1 = 0`, a contradiction.

*Verification by `w3-vf-linear` (2026-09-12), Section 27.1 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: PASS. Recomputed: the inclusion–exclusion isolating Sym_ij; T_a S_b = [a=b] P_2 with the (n!)^-1 normalization; rk P_1 >= 2 rk P_2 = 2 rk P_1 via w = [[0,1,0],[−1,0,0],[0,0,1]]; and Möbius inversion of 1^(⊗n) over unions of at most n of the n+1 pieces.*
