---
rg: 2
id: weakly-finite-image-from-state-upgrade
kind: route
title: The state upgrade gives a rank model moving minus one, hence a rank function on the summand, hence a weakly finite image
target: anti-central-rank-condition-gives-weakly-finite-image
requires: [ternary-anti-central-states-force-nontrivial-rank-models, ternary-leavitt-rank-models-move-z-iff-nontrivial, anti-central-rank-functions-give-weakly-finite-leavitt-images, anti-central-state-obstruction-equals-stable-finiteness]
artifacts:
  - research/artifacts/state-upgrade-rank-condition-gap-2026-09-12.md
---

Artifact Section 1.
1. The rank condition on `S_-` gives a state (part 2 of `anti-central-state-obstruction-equals-stable-finiteness`).
2. The upgrade gives a nontrivial characteristic-three rank model of `G_3`, which moves `z` by
   `ternary-leavitt-rank-models-move-z-iff-nontrivial`.
3. **A rank function on the summand.** Composing with the normalized rank of the ultraproduct gives a
   Sylvester matrix rank function `rk` on `F_3[G_3]` with `rk(1 - [z]) > 0`.
   - `rk(eps_-) > 0`, so the corner normalization `N(X) = rk(X eps_-)/rk(eps_-)` is a rank function on
     `S_-` with `N(eps_-) = 1`.
4. `anti-central-rank-functions-give-weakly-finite-leavitt-images` gives the weakly finite image.

This route only records that the target is necessary for the upgrade. It is not an independent proof.
