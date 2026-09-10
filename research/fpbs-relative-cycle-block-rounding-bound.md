---
rg: 2
id: fpbs-relative-cycle-block-rounding-bound
kind: claim
title: Weighted boundary localization of a relative cycle operator gives connected block rounding
distinct_from:
  fpbs-short-cycle-edge-measure-vanishes-near-optimum: that deletes edges by shortest-cycle priority; this simultaneously replaces disjoint connected blocks by trees and bounds lost relative trace using the block Laplacian
  fpbs-relative-cycle-dpp-disconnects: that disproves connectedness of a determinantal rule; this gives a deterministic connected subgraphing with an explicit weighted boundary error
artifacts:
  - research/artifacts/fpbs/docs/relative-cycle-exchange.md
---

Let H generate an aperiodic p.m.p. relation with degree at most d, and
let 0<=K<=P_Z(H) be an equivariant positive contraction. For a measurable
partition E into H-connected blocks of at most M vertices, let P_out
project onto edges crossing between blocks and b=Tr(P_out K). Replacing
each block interior by a spanning tree and retaining all crossing
edges gives a generating H' contained in H with

    c(H') <= c(H)-Tr(K)+(1+2d M^2)b.

If K is the relative operator for a source graphing Phi as in
`fpbs-relative-cycle-operator-descent`, this is
C(X)<=c(H')<=c(Phi)+(1+2d M^2)b.

Section 6 supplies the written proof. It is a conditional quantitative
rounding estimate, not a construction of partitions making its error
small, a formal verification, or a claim of mathematical priority.
