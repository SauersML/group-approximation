---
rg: 2
id: sl3-finite-building-label-descent-proof
kind: route
title: Apply the deck-transformation descent criterion and compare left labels with Hecke relative positions
target: sl3-finite-building-quotients-forget-arithmetic-labels
requires: []
artifacts:
  - research/artifacts/sl3-building-quotient-label-audit-2026-08-21.md
---

The building is simply connected and `Gamma` acts freely, so its elements
are the deck transformations of `X -> Gamma\X`.  The lift `L_a` descends
exactly when conjugation by it preserves the deck group, namely when
`a Gamma a^(-1)=Gamma`.  This proves `(FBL1)`.

For the second assertion, the pair `(gK,gaK)` has constant relative
position `KaK`, whereas the image of `gK` under the fixed left action is
`agK`, whose relative displacement in the frame at `gK` is `g^(-1)ag`.
Hence the unlabelled Hecke correspondence contains different data from the
fixed arithmetic generator.  Neither injectivity radius nor unlabelled
local convergence supplies the missing coherent frames.
