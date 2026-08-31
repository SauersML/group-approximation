---
rg: 2
id: stw22-row-amplified-high-low-s5-transfer-proof
kind: route
title: Transfer diffuse five-sphere fillings through the rectangular high-low decomposition
target: stw22-diffuse-weighted-copy-uniform-s5-fillings
requires:
  - stw22-diffuse-stiefel-uniform-five-sphere-fillings
  - stw22-diffuse-relative-low-spectrum-six-ball-extension
  - stw22-diffuse-weighted-copy-uniform-s4-fillings
artifacts:
  - research/artifacts/stw22-dim6-factor-bundle-breakthrough-2026-08-31.md
---

Encode all copies in the first row of `M_m(N)`.  The normalized first-corner
metric is exactly the tuple Hilbert-sum metric.  With
`eta=(min(epsilon,1)/12)^2`, the high polar sphere amplifies input by
`eta^(-1/2)` and fills by the diffuse Stiefel theorem.  The conservative
input radius is `min(epsilon,1)^3/216000000`.  Apply the relative six-ball
theorem to the whole low row; its tuple cost is at most
`2sqrt(m tau(ap_l))<=2sqrt(eta)`.  Recombination gives the exact filling.
The same argument without estimates proves global fiveconnectivity.

