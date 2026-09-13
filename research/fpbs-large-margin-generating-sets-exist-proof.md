---
rg: 2
id: fpbs-large-margin-generating-sets-exist-proof
kind: route
title: Remove the identity from Thom's generating sets and bound expansion by degree minus norm
target: fpbs-large-margin-generating-sets-exist
requires:
  - fpbs-thom-small-spectral-radius-generating-sets
artifacts:
  - research/artifacts/fpbs-single-product-move-2026-09-12.md
---

Notation as in the target. Section 5 of the artifact carries the same proof.

1. Choose `epsilon ∈ (0, 1/4]` with `epsilon^{-2}/2 - 2 > K`. By
   `fpbs-thom-small-spectral-radius-generating-sets` there is a finite
   symmetric generating set `S_0` with `rho(S_0) < epsilon`.
2. Put `M = |S_0|^{-1} sum_{s ∈ S_0} lambda(s)`. The vectors `delta_s` are
   orthonormal, so `rho(S_0) = ||M|| >= ||M delta_e|| = |S_0|^{-1/2}`. Hence
   `|S_0| > epsilon^{-2}`.
3. Put `S = S_0 \ {e}`, which is symmetric and still generates `Gamma`.
   - Conjugating by `f ↦ f∘inv` turns `A_{S_0}` into `|S_0| M`, so
     `||A_{S_0}|| < epsilon |S_0|`.
   - `A_S` equals `A_{S_0}` or `A_{S_0} - I`, so `||A_S|| <= epsilon|S_0| + 1`.
   - `|S| >= |S_0| - 1`.
4. For finite `F`, `<A_S 1_F, 1_F> = |S||F| - |∂_E F|`, since `Cay(Gamma,S)` is
   simple and each boundary edge is counted once from its endpoint in `F`. So
   `h(S) >= |S| - ||A_S||`.
5. Hence
   `1 + h(S) - ||A_S|| >= 1 + |S| - 2||A_S|| >= |S_0|(1 - 2 epsilon) - 2`.
   Since `epsilon <= 1/4` and `|S_0| > epsilon^{-2}`, this is at least
   `|S_0|/2 - 2 > epsilon^{-2}/2 - 2 > K`.
