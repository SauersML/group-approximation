---
rg: 2
id: thompson-v-pair-bernoulli-not-sofic-from-v-not-sofic
kind: route
title: A nonsofic V has no sofic actions, in particular not over V/V_[0]
target: thompson-v-cantor-pair-bernoulli-action-is-not-sofic
requires: [thompson-v-not-sofic]
---

A sofic p.m.p. action `V ↷ (Z, zeta)` is a trace-preserving embedding
`Theta : L^∞(Z) ⋊ V -> prod_omega M_(n_k)(C)` with `L^∞(Z)` diagonal and every
`Theta(u_g)` a permutation matrix (Păunescu Definition 1.4). The canonical trace
vanishes on `u_g` for `g != 1`, so `g -> Theta(u_g)` is an injective homomorphism into
the universal sofic group, and `V` is sofic. This is the remark already recorded in
`kun-thom-free-nonsofic-action` ("a group with a sofic action is sofic, whether or not
the action is free").

Contrapositive: under `thompson-v-not-sofic`, no action of `V` is sofic, in particular
the generalized Bernoulli action over `V/V_[0]`.
