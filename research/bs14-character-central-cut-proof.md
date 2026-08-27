---
rg: 2
id: bs14-character-central-cut-proof
kind: route
title: Cut the ultraproduct by the finite and regular character faces
target: bs14-character-split-leaves-only-the-regular-microstate-face
requires:
  - character-rigidity-equals-hyperfinite-hs-stability
  - bs14-global-atoms-are-moving-congruence-restrictions
  - residual-finite-tensor-camouflages-iwahori-transfer-failures
---

Apply the Peterson--Thom extreme-character dichotomy and integrate its two
measurable faces to obtain the central projection in `(CSR2)`.  Projections
in a tracial matrix ultraproduct lift to matrix projections; commutation with
`pi(A)` is exactly `(CSR3)`.  Compressing an almost-invariant projection and
taking the polar part changes each fixed generator by `o(1)` in normalized
HS norm.

The finite-character corner is a direct integral of matrix algebras, hence
hyperfinite, and the cited hyperfinite stability theorem corrects it.  On
the complementary corner all extremal characters equal `delta_e`, so their
integral equals `delta_e`; its GNS algebra is `L(A)`.  The tensor-camouflage
claim records why canonical-character conditioning cannot eliminate a
tensor-stable obstruction.

