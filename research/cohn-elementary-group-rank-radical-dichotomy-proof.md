---
rg: 2
id: cohn-elementary-group-rank-radical-dichotomy-proof
kind: route
title: Basis embeddings, the finitary kernel as a simple group with trivial centralizer, and simplicity of the Leavitt quotient
target: cohn-elementary-group-rank-radical-is-trivial-or-everything
requires:
  - binary-leavitt-unit-group-is-simple
  - leavitt-gl-equals-el-and-perfect-unit-group
artifacts:
  - research/artifacts/cohn-elementary-group-rank-radical-2026-09-12.md
---

Artifact Section 2, Lemmas 2.1 to 2.3 and Theorem 2.4.

1. **Embeddings.**
   - `J -> C_2` and `C_2 -> L(1,3)` send normal-form bases to basis words. In `L(1,3)`, words over
     `{0,1}` never end in the special edge.
   - `L(1,3) -> R` is `s_0 -> s_0`, `s_1 -> s_1 s_0`, `s_2 -> s_1 s_1`, injective by simplicity.
   - `GL_3(R) = EL_3(R)` (`leavitt-gl-equals-el-and-perfect-unit-group`), and `M_3(R) ~ R`, so
     `EL_3(R) ~ R^x`, which is simple (`binary-leavitt-unit-group-is-simple`).
2. **Kernel.**
   - `(q)` is spanned by the matrix units `s_mu q t_nu`, so `ker pi <= GL_fin(W x 3, F_2)`.
   - Transvections between different rows are `x_ab(s_mu q t_nu)`, and those within one row are
     commutators through a third row. So `K <= G`.
   - Finitary `SL` over an infinite basis is simple.
   - Operators commuting with every `E_(x,y)` are scalars, so `C_G(K) = 1`.
3. **Normal subgroups.** Take `N` normal in `G`.
   - `N ∩ K` is `1` or `K`.
   - If it is `1`, `[N, K] = 1`, so `N = 1`.
   - If `N >= K`, then `N/K` is normal in the simple group `EL_3(R)`.
4. **Radical.** It is normal, so it is `1`, `K` or `G`.
   - If it were `K`, some nontrivial model would factor as `tau o pi`. `tau` is injective by
     simplicity, and `tau o iota` with `iota : G -> EL_3(R)` is injective on `G`, which contradicts
     the radical being `K`.
   - So a model with kernel `K` yields an injective model as well.
