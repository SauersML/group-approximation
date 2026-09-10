---
rg: 2
id: fpbs-relative-cycle-block-rounding-bound-proof
kind: route
title: Bound noninternal cycle energy by crossing-edge energy and count deleted block cycles
target: fpbs-relative-cycle-block-rounding-bound
requires:
  - fpbs-relative-cycle-operator-descent
artifacts:
  - research/artifacts/fpbs/docs/relative-cycle-exchange.md
---

Section 6. Let P_0 project onto internal block cycles. For a full cycle
chain v, its internal part orthogonal to P_0 is a gradient whose
boundary is the negative boundary of its external part. The block
Laplacian lower bound 1/M^2 and the full boundary norm bound sqrt(2d)
give ||(I-P_0)v||^2<=(1+2d M^2)||P_out v||^2. Apply this to K^(1/2)
and take traces. Since Tr(P_0 K)<=Tr(P_0), internal block cycle
dimension is at least Tr(K) minus the stated error. Replacing each
block by a tree deletes exactly that dimension in edge measure and
preserves every original connection. The required relative-operator
identity substitutes Tr(K)=c(H)-c(Phi) for the last assertion.
