---
rg: 2
id: uniform-diffuse-profile-tail-no-go-proof
kind: route
title: Observe that every nonempty level set lies above the small-set cutoff
target: operator-tail-contraction-misses-uniform-diffuse-matching
requires:
  - all-dual-unique-neighbors-contract-operator-tails
---

For `(UDM1)`, `U_t=[L]` when `t<=a_L` and `U_t` is empty when `t>a_L`.
The hypothesis `|U_t|<=alpha L` therefore never holds for a nonempty tail.
At the same time `(1/L)sum_i q_i^2=a_L^2`, proving that arbitrarily small
average energy alone does not move the profile into the contraction regime.
