---
rg: 2
id: cohn-el3-two-root-identity-from-jacobson-rank-radical
kind: route
title: A head-killing Jacobson radical forbids injective models of the Cohn elementary group, which then has no nontrivial model
target: cohn-coefficient-el3-rank-models-satisfy-two-root-identity
requires:
  - binary-jacobson-el3-rank-radical-is-the-finitary-kernel
  - cohn-elementary-group-rank-radical-is-trivial-or-everything
  - two-root-identity-in-all-models-iff-no-nontrivial-model
artifacts:
  - research/artifacts/cohn-elementary-group-rank-radical-2026-09-12.md
---

Artifact Section 3, Corollary 3.2.

1. **The head.** `S -> s_0`, `T -> t_0` embeds `EL_3(J)` in `G = EL_3(C_2)`. The Jacobson head
   `x_13(1 - ST)` maps to the nontrivial element `x_13(1 - s_0 t_0)`.
2. **The radical of `G` is everything.** By the Jacobson claim every characteristic-two rank model of
   `EL_3(J)` kills that head. So no model of `G` retains it, and the rank radical of `G` is not `1`.
   By `cohn-elementary-group-rank-radical-is-trivial-or-everything`, it is `G`.
3. **The identity.** Every model of `G` is trivial, so `N_23 N_12 = 0` holds in each of them
   (`two-root-identity-in-all-models-iff-no-nontrivial-model`, the easy direction).

This route is live but does not discharge the target: the Jacobson claim is OPEN.
