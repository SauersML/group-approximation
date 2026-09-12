---
rg: 2
id: fpbs-relative-cycle-retraction-rounding
kind: claim
title: A bounded path retraction gives connected rounding with residual cycle energy as its cost error
distinct_from:
  fpbs-relative-cycle-block-rounding-bound: that charges weighted crossing-edge mass before cancellation; this measures the signed chain image after replacement and also permits one retained bridge per adjacent block pair
  fpbs-relative-cycle-operator-descent: that constructs a base relative operator with exact trace; this bounds the cost of a specified connected retained graphing using the operator's image under a path retraction
artifacts:
  - research/artifacts/fpbs/docs/relative-cycle-exchange.md
---

Let H be a bounded-degree generating graphing and J a measurable
spanning subgraph. Suppose finite J-path replacements of H-edges
define a bounded equivariant operator R that fixes every retained
edge. For every equivariant positive contraction K on the edge module,

    c(J)<=c(H)-Tr(K)+Tr(R K R^*).

The path replacements prove that J generates. For the relative cycle
operator of a source graphing Phi, this gives
C(X)<=c(J)<=c(Phi)+Tr(R K R^*).

Section 7 supplies the proof and a bounded construction retaining
block trees and one bridge per adjacent block pair. With degree d and
block size M its paths have length at most 2M-1 and edge congestion
at most dM. On the fixed F_r x C_M certificate from Section 2 the
residual vanishes, although its weighted boundary cannot vanish.

This is a written deduction, not a universal residual bound, a
formal verification, or a claim of mathematical priority.
