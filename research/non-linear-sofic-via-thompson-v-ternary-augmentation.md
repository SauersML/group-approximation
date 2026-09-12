---
rg: 2
id: non-linear-sofic-via-thompson-v-ternary-augmentation
kind: route
title: If every Sylvester rank function on F_3[V] is the augmentation rank, Thompson's V is not F_3-linear sofic
target: non-linear-sofic-group
requires: [thompson-v-ternary-rank-functions-are-augmentation]
artifacts:
  - research/artifacts/gottschalk-region-synthesis-2026-09-12.md
  - research/artifacts/signed-thompson-minus-one-gate-is-v-rank-gate-2026-09-12.md
---

Wiring. Before this route, `thompson-v-ternary-rank-functions-are-augmentation` had one outgoing route, into
the ternary counterexample chain, and none into the landmark. It is the linear-sofic version of
`thompson-v-ternary-nonaugmentation-rank-function-from-soficity`.

1. Suppose `V` is `F_3`-linear sofic. Then there are maps `phi_k : V -> GL_(n_k)(F_3)` that are asymptotically
   multiplicative in normalized rank, with `rk(phi_k(g) - 1)/n_k >= c_g > 0` for each `g != 1`.
2. In the rank ultraproduct `M` of the `M_(n_k)(F_3)`, the limit `phi : V -> M^x` is a homomorphism with
   `rk(phi(g) - 1) >= c_g`.
3. Extend `phi` linearly to a unital ring map `F_3[V] -> M`. Pulling back the normalized rank of matrices over
   `M` gives a Sylvester matrix rank function on `F_3[V]` with `rk(1 - [g]) >= c_g > 0`. That contradicts the
   requirement.
4. So `V` is not `F_3`-linear sofic. `V` is countable, which witnesses `non-linear-sofic-group` with `F = F_3`.

The requirement is open, so the route does not fire.
