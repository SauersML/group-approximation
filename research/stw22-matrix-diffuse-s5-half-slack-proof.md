---
rg: 2
id: stw22-matrix-diffuse-s5-half-slack-proof
kind: route
title: Half slack and m at least three force the matrix codimension-three regime
target: stw22-half-slack-all-factor-weighted-s5-fillings
requires:
  - stw22-diffuse-weighted-copy-uniform-s5-fillings
  - stw22-matrix-weighted-copy-codim3-uniform-s5-fillings
  - stw22-half-slack-all-factor-weighted-copy-uniform-s4-fillings
artifacts:
  - research/artifacts/stw22-dim6-factor-bundle-breakthrough-2026-08-31.md
---

The diffuse theorem applies under strict slack.  In `M_n`, a nonzero weight
has total rank `k=m rank(p)>=3`; half slack gives `k<=n/2`, hence unused
rank `c=n-k>=n/2>=3`.  The matrix codimension-three theorem applies.  Its
modulus is larger than the diffuse modulus, so the latter works in both
branches.  Zero weights are singletons, and the pointwise dichotomy needs
no continuous type stratum.

