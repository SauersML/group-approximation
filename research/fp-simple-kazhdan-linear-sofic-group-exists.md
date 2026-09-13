---
rg: 2
id: fp-simple-kazhdan-linear-sofic-group-exists
kind: claim
title: Some finitely presented infinite simple Kazhdan group is linear sofic over a finite field
distinct_from:
  hyperlinear-fp-infinite-simple-group: that is the existence root for hyperlinear finitely presented simple groups; this asks for rank-metric approximability over a finite field, which is weaker than soficity and not known to imply hyperlinearity.
  sofic-fp-simple-kazhdan-group-from-fp-simple-ring: that asks for soficity; this is the rank-metric milestone the ring route reaches with gate (c) removed.
  non-linear-sofic-simple-groups-bounded-width-in-classical-groups: that constrains finitely presented simple groups that are NOT linear sofic; this asks for one that IS.
---

**OPEN.** There is a finitely presented infinite simple group with property (T) that embeds in a
rank ultraproduct of `GL_N(F_q)` for some prime power `q`.

**Status of the question.** No finitely presented infinite simple group with any metric
approximation property (sofic, hyperlinear, linear sofic) is recorded in this graph. That was a
bounded check of the graph and of the arXiv listing record in
`research/artifacts/ex-open-status-2026-09-12.md`, which covers sofic and hyperlinear.

## Attempts

- **Ring route with a rigid free minimal SFT.** Route
  `fp-simple-kazhdan-linear-sofic-via-rigid-free-minimal-sft`. It needs a quantum rigid free minimal
  `Z^2`-SFT and gate (b).
- **Leavitt-type rings: dead.** Halvable corners make the groups nonsofic
  (`halvable-corner-makes-elementary-groups-nonsofic`). The rank-metric row for the Leavitt instance
  (`leavitt-el3-rank-models-over-finite-fields-are-trivial`) is open, and no ring rank model exists
  there (`leavitt-algebra-has-no-unital-rank-model`).
- **Kac--Moody and Titz Mite--Witzel lattices.** Owned by neighbouring lanes; no rank model is
  recorded.
