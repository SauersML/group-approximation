---
rg: 2
id: fanizza-mixed-selector-transvection-countermodel-proof
kind: route
title: Put a Pauli anticommuting pair on the negative D8 guard sector
target: fanizza-mixed-selector-transvection-retains-guard-mass
requires: []
artifacts:
  - research/artifacts/fanizza-mixed-selector-transvection-audit-2026-08-21.md
---

On a `2m`-dimensional block take `K=-I`, `Z=sigma_z tensor I_m`, and
`S=sigma_x tensor I_m`.  Then `SZS^*=-Z=KZ`.  On a `14m`-dimensional
complement take all three involutions equal to `I`.  Their direct sum
satisfies every relation exactly, while the negative `K` projection has
normalized rank `2m/(16m)=1/8`.

Conversely, `(MST6)` maps the positive `Z` eigenspace in the negative `K`
sector unitarily onto the negative eigenspace, proving only equality of the
two ranks.  Arbitrary common amplification is allowed, so no defect bound
can control their sum or `tr(H)`.
