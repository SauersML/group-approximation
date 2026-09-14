---
rg: 2
id: fp-simple-groups-escape-soft-hyperlinear-permanence
kind: claim
title: Marked limits and residual amenability cannot certify a non-amenable finitely presented simple group
invalidates:
  - hyperlinear-fp-simple-via-marked-limits
  - hyperlinear-fp-simple-via-residual-amenability
distinct_from:
  hyperlinear-fp-infinite-simple-group: That is the open existence root; this proves that two soft certificate families collapse on its candidates.
  fg-simple-hyperlinear-tree-group-not-finitely-presented: That calibrates the live amenable-edge splitting route; this kills the marked-limit and residual-amenability routes.
---

**ESTABLISHED.**  Let `S` be a finitely presented infinite simple group.

1. **Isolation.**  `S` is an isolated point of the space of marked groups.
   So if a sequence of hyperlinear marked groups converges to `S`, it is
   eventually equal to `S`.
2. **Residual collapse.**  If `S` is residually amenable, or locally
   embeddable into amenable groups (LEA), then `S` is amenable.

Consequently neither Chabauty approximation by hyperlinear groups nor
residual/local amenability can be the source of a hyperlinearity certificate
for a non-amenable finitely presented infinite simple group.  The amenable
case is untouched: no finitely presented infinite simple amenable group is
recorded in this graph.

Proof: `fp-simple-soft-permanence-proof`.
