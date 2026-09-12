---
rg: 2
id: anti-central-rank-functions-weakly-finite-image-proof
kind: route
title: Pull the rank function back along the central idempotent; its null subgroup misses minus one, so it is trivial
target: anti-central-rank-functions-give-weakly-finite-leavitt-images
requires: [sylvester-rank-function-quotients-are-weakly-finite, simple-group-rank-functions-are-augmentation-or-detecting, odd-leavitt-unit-groups-mod-scalars-are-fp-simple, leavitt-gl-equals-el-and-perfect-unit-group]
artifacts:
  - research/artifacts/state-upgrade-rank-condition-gap-2026-09-12.md
---

Artifact Corollary A.2.
1. `X -> X eps_-` is a unital ring map `F_3[G_3] -> S_-`, since `eps_-` is a central idempotent. So
   `rk(X) = N(X eps_-)` is a Sylvester matrix rank function.
2. Its null subgroup `N_rk` is normal. `rk(1 - [z]) = N(2 eps_-) = 1`, so `z` is not in `N_rk`.
3. A normal subgroup missing `z` meets `<z>` trivially, and its image in the simple group `PG` is `1`
   or `PG`. If the image is `PG`, then `G_3 = N_rk × <z>` has a quotient of order two, contradicting
   perfection. So `N_rk = 1`.
4. The quotient by `ker N` is weakly finite with a faithful rank function
   (`sylvester-rank-function-quotients-are-weakly-finite`). Faithfulness and `N_rk = 1` give the
   embedding of `G_3`.
