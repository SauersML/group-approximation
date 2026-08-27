---
rg: 2
id: literal-kazhdan-clifford-inputs-proof
kind: route
title: Rational spectral and affine-matrix proof of the literal inputs
target: literal-kazhdan-clifford-inputs
requires: []
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/LiteralBaseP13PropertyTBridge.lean
  - GroupApproximation/Sofic/LiteralNonMFLinearWitness.lean
  - GroupApproximation/Sofic/LiteralP13HodgeCertificate.lean
---

## Direct proof

The literal base is certified with a rational spectral gap at least `1/500`.
In the displayed affine model, conjugation by
`diag(2,2,2,1)` doubles each integral translation and fixes the linear
generators.  The inverse image of `v_1` would be translation by `e_1/2`,
which is not integral.  The cited Lean artifacts check both the literal
presentation bridge and the separating linear model without caller-supplied
mathematical premises.
