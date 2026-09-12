---
rg: 2
id: hyperlinear-non-mf-from-sofic-witness
kind: route
title: Apply the permutation-matrix embedding to the sofic non-MF witness
target: hyperlinear-not-imply-mf
requires: [sofic-non-mf-witness, sofic-implies-hyperlinear]
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Endpoint/NonMFImpact.lean
  - GroupApproximation/Sofic/Hyperlinear.lean
---

## Why sufficient

Sofic approximations become hyperlinear approximations by inverse permutation
matrices, using
`||P_sigma-P_tau||^2_HS,norm = 2 d_H(sigma,tau)`.  Applying this established
implication to the sofic non-MF group `W` produces the required hyperlinear
non-MF witness.
