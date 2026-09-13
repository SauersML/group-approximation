---
rg: 2
id: normal-kazhdan-via-infranormal-detection
kind: route
title: Specialize infranormal detection to a normal subgroup in a compression defect
target: normal-kazhdan-defect-non-mf
requires:
  - virtually-infranormal-kazhdan-mf-detection
  - kazhdan-asymptotic-commutant-transport
artifacts:
  - research/artifacts/infranormal-mf-detection-2026-09-13.md
---

If `K` is normal in `G`, every element compresses `K`, so its
compressor-generated subgroup is all of `G`. For a property-(T) subgroup
`L`, one-sided transport puts `D_G(L)` in `S(G)`: a centralizing element's
conjugate remains in the asymptotic commutant, so each defect commutator
tends to the identity in normalized HS norm, as does its normal closure.
For `K <= D_G(L)` the new detector therefore gives `K <= Rad_MF(G)`.
