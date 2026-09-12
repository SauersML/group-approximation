---
rg: 2
id: cohn-elementary-group-rank-radical-is-trivial-or-everything
kind: claim
title: The binary Cohn elementary group EL_3(C_2) embeds in the binary Leavitt unit group and has rank radical 1 or everything
distinct_from:
  binary-jacobson-mark-dichotomy-holds-from-rank-two: that is the one-pair Jacobson algebra, whose symbol quotient is residually finite, so its radical is 1 or the finitary kernel; this is the two-pair Cohn algebra, whose quotient is the simple group R^x, so the finitary kernel is excluded and the radical is 1 or the whole group.
  binary-jacobson-el3-rank-radical-is-the-finitary-kernel: that asks whether every rank model of EL_3(J) kills its finitary kernel; this is a proved structure theorem for EL_3(C_2), under which the corresponding question becomes whether every rank model is trivial.
artifacts:
  - research/artifacts/cohn-elementary-group-rank-radical-2026-09-12.md
---

**ESTABLISHED** (proof route `cohn-elementary-group-rank-radical-dichotomy-proof`; artifact Section 2;
independent re-derivation requested from `w4-vf-gate`).

**Setting.**
* `C_2 = F_2<s_0, s_1, t_0, t_1 | t_i s_j = delta_ij>` and `q = 1 - s_0 t_0 - s_1 t_1`.
* `R = L_(F_2)(1,2) = C_2/(q)`, `J = F_2<S, T | TS = 1>` and `W = {0,1}^*`.
* `G = EL_3(C_2)` and `pi : G -> EL_3(R)`.

**Statement.**
1. **Embeddings.** There are unital embeddings `J -> C_2 -> L_(F_2)(1,3) -> R`, so
   `EL_3(J) <= G <= EL_3(R) = GL_3(R) ~ R^x`.
2. **Finitary kernel.** `ker pi = K = GL_fin(W x {1,2,3}, F_2)`, acting on `F_2[W]^3` through the
   faithful Toeplitz representation. `K` is infinite and simple, and `C_G(K) = 1`.
3. **Normal subgroups.** The normal subgroups of `G` are `1`, `K` and `G`.
4. **Rank radical.** The intersection of the kernels of all characteristic-two rank models of `G` is
   `1` or `G`. So `G` has a nontrivial characteristic-two rank model iff it has an injective one.

**Consequences** (artifact Section 3).
* **The target, restated.** Together with `two-root-identity-in-all-models-iff-no-nontrivial-model`,
  `cohn-coefficient-el3-rank-models-satisfy-two-root-identity` holds iff `EL_3(C_2)` has no injective
  characteristic-two rank model.
* **The chain.** `binary-jacobson-el3-rank-radical-is-the-finitary-kernel` implies that claim, and
  that claim implies that `R^x` has no nontrivial characteristic-two rank model (route
  `cohn-el3-two-root-identity-from-jacobson-rank-radical`).
* **Completeness.** It is load-bearing for the binary gate exactly when `EL_3(C_2)` is
  characteristic-two linear sofic.
