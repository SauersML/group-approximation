---
rg: 2
id: regular-mf-tensor-sync-proof
kind: route
title: Tensor the common regular base model with conjugate finite edge models
target: regular-mf-tensor-sync-proves-twisted-rope-mf
requires: []
artifacts:
  - research/artifacts/regular-mf-tensor-synchronized-rope-2026-08-25.md
  - research/artifacts/profinite-synchronized-hnn-proof-2026-08-25.md
---

For `A_n=C_n times B_n`, the two maps

```text
s |-> (lambda_n(s),1),
s |-> (lambda_n(s),beta_n(tau(s)))
```

have equal kernels by `(RTS1)`.  Their restrictions in the left regular
representation of the finite image are therefore exactly unitarily
conjugate.  Tensor these representations with coordinate lifts of a regular
matrix-corona model of `Gamma`.  The common `Gamma` matrix is unchanged on
the two edges, so the finite conjugator gives exact edge compatibility in the
tensor corona.

The tensor model has the regular character on `Gamma times Q`: the regular
base trace kills `g!=1`, and the cofinal regular finite quotients kill
`q!=1` when `g=1`.  Apply Ueda's universal-HNN corner construction and
Shulman's compatible-corona criterion, then use the reduced von Neumann HNN
normal form for this regular trace to separate every Britton-reduced word.
