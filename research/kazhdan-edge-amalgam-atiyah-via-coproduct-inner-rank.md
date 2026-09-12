---
rg: 2
id: kazhdan-edge-amalgam-atiyah-via-coproduct-inner-rank
kind: route
title: Maximality of the coproduct rank gives Strong Atiyah for the Kazhdan-edge amalgam
target: strong-atiyah-kazhdan-edge-amalgam-permanence
requires:
  - atiyah-amalgam-rank-from-cohn-coproduct
  - kazhdan-edge-coproduct-rank-is-inner-rank
artifacts:
  - research/artifacts/atiyah-vertex-mixing-2026-09-12.md
---

Under the hypotheses of `strong-atiyah-kazhdan-edge-amalgam-permanence`,
`kazhdan-edge-coproduct-rank-is-inner-rank` gives `rk_G(phi(Y)) = rho_R(Y)` for every matrix `Y`
over `R = D_A *_(D_C) D_B`. Part (4) of `atiyah-amalgam-rank-from-cohn-coproduct` turns that
equality into integrality of `rk_G` on every matrix over `K[G]`, which is Strong Atiyah over `K`
for `G`.
