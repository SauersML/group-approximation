---
rg: 2
id: stw22-row-amplified-all-finite-degree-transfer-proof
kind: route
title: Apply the same high-low row transfer in every finite sphere degree
target: stw22-diffuse-weighted-copy-all-finite-sphere-fillings
requires:
  - stw22-diffuse-stiefel-all-finite-sphere-fillings
  - stw22-diffuse-relative-low-spectrum-all-finite-balls
artifacts:
  - research/artifacts/stw22-diffuse-all-degree-induction-audit-2026-08-31.md
---

Fix a finite `d`. Encode all copies as one rectangular first row in
`M_m(N)`. The normalized corner metric is exactly the tuple Hilbert-sum
metric. Split the fixed weight at `eta=(epsilon_0/12)^2`.

The high polar `S^d` fills by the all-degree Stiefel theorem at cost
`epsilon_0/3` when the weighted input radius is

```text
sqrt(eta)rho_St(epsilon_0/3)/2
 =epsilon_0^3/216000000.                                (AD-5)
```

The all-degree relative theorem fills the entire low row in the moving
complement, preserving every cross relation, with tuple cost at most
`2sqrt(m tau(ap_l))<=epsilon_0/6`. Recombine. Global `d`-connectivity
uses an arbitrary high fill followed by the same relative low extension.
Because the construction and estimates do not depend on `d`, (AD-4) holds
in every finite degree.