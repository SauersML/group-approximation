---
rg: 2
id: hyperlinear-models-need-quadratic-dimension
kind: claim
title: Hypothetical hyperlinear models of the saturated group need dimension inverse-quadratic in their relator defect
distinct_from:
  dimension-defect-controlled-mf-hyperlinear: that says operator-norm models whose defect beats inverse dimension already produce hyperlinearity, for an arbitrary countable group; this bounds the dimension of a hypothetical normalized-HS model of one particular group from below.
  full-mf-radical-hyperlinear-models-force-relator-outliers: that produces a fixed relator and a vanishing-trace spectral corner carrying its operator-norm failure; this produces a numerical floor on the dimension and names no corner.
  full-mf-radical-linear-relator-inequality: that is the operator-norm inequality itself; this is the normalized Hilbert--Schmidt reading of it, which is strictly weaker than a defect gap.
artifacts:
  - research/artifacts/hs-defect-gap-and-padding-2026-09-07.md
  - research/artifacts/mf-radical-linear-certificate-2026-09-07.md
---

Let `Q=<S|R>` be the finite presentation of
`defect-saturation-full-mf-radical` and let `C` be the constant of
`full-mf-radical-linear-relator-inequality` for a relator list contained in
`R`.  Then every `d` and every `U in U(d)^S` with `D_2(U) >= 1` in
normalized Hilbert--Schmidt norm satisfy

```text
d >= 1 / (C^2 d_2(U)^2).
```

A microstate sequence for a hyperlinear `Q` has `d_2 -> 0` and
`D_2 -> sqrt 2`, so its dimensions grow at least like `d_2^(-2)`.  Microstate
dimensions are unconstrained, so this refutes nothing; it is the exact
quantitative residue that the operator-norm certificate leaves.
