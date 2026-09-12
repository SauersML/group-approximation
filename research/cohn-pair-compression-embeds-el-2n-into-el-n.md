---
rg: 2
id: cohn-pair-compression-embeds-el-2n-into-el-n
kind: claim
title: A Cohn pair compresses EL_2n into EL_n, so EL_3 over the binary Cohn algebra contains every EL_m over it, every EL_m over the Jacobson algebra, and Thompson's V
distinct_from:
  thompson-v-lifts-into-rank-four-cohn-elementary-group: that lifts V into GL_2(C_2) and EL_4(C_2); this compresses EL_2n(S) into EL_n(S) for any ring with a Cohn pair, which puts EL_4(C_2), and hence V, inside EL_3(C_2).
  cohn-elementary-group-rank-radical-is-trivial-or-everything: that computes the normal subgroups and rank radical of EL_3(C_2); this embeds every EL_m(C_2) and every EL_m(J) in EL_3(C_2).
artifacts:
  - research/artifacts/cohn-elementary-group-compressions-and-lef-2026-09-12.md
---

**ESTABLISHED** (proof route `cohn-pair-compression-el-embedding-proof`; artifact Sections 1–2;
independent re-derivation requested from `w4-vf-gate`).

**Setting.** `S` is a unital ring, and `s_0, s_1, t_0, t_1 in S` satisfy `t_i s_j = delta_ij`. Put
`q = 1 - s_0 t_0 - s_1 t_1` and `iota(x) = sum_(a,b) s_a x_ab t_b` on `M_2(S)`. Apply `iota`
blockwise to `M_(2n)(S) = M_n(M_2(S))`.

1. **Homomorphism.** `psi_n(g) = iota_n(g) + q 1_n` is an injective group homomorphism
   `GL_(2n)(S) -> GL_n(S)`, and `psi_n(x_((i,a),(j,b))(c)) = x_ij(s_a c t_b)` for `i != j`.
2. **Elementary image.** For `n >= 2`, `psi_n(EL_(2n)(S)) <= EL_n(S)`, because same-block generators
   are commutators of cross-block ones.
3. **Binary Cohn algebra.**
   - `EL_m(C_2)` embeds in `EL_n(C_2)` for all `m, n >= 2`.
   - `EL_m(J) <= EL_3(C_2)` for every `m`, where `J = F_2<S,T | TS=1>`.
   - `EL_n(C_2)` has an injective characteristic-two rank model iff `EL_3(C_2)` does.
   - `psi_n` maps the finitary kernel `ker(EL_(2n)(C_2) -> EL_(2n)(R))` into the finitary kernel,
     and elements outside it to elements outside.
4. **V in rank three.** With `thompson-v-lifts-into-rank-four-cohn-elementary-group`, `V` embeds in
   `EL_3(C_2)` and meets its finitary kernel `K` trivially.
   - **Consequence:** `thompson-v-has-no-nontrivial-f2-rank-model` makes every characteristic-two rank
     model of `EL_3(C_2)` trivial (route `cohn-coefficient-el3-two-root-identity-from-v-gate`).
   - **Dependency:** this item consumes the rank-four lift, which is landed ESTABLISHED and still
     awaiting its own verification.
