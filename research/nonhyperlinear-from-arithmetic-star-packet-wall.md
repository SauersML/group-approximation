---
rg: 2
id: nonhyperlinear-from-arithmetic-star-packet-wall
kind: route
title: Contradict positive-density Kazhdan commutant no-growth with the S9 Reynolds wall
target: non-hyperlinear-group
requires:
  - arithmetic-star-packet-carrier
  - arithmetic-star-packet-hs-plancherel-anchor
  - arithmetic-star-packet-hs-wall-placement
  - property-t-hs-positive-density-commutant-no-growth
artifacts:
  - notes/ARITHMETIC_STAR_PACKET_HYPERLINEAR_AUDIT.md
---

**CLOSED ROUTE.**  Its wall-placement premise is refuted by
`arithmetic-star-packet-is-sofic`: the proposed carrier embeds in a sofic
graph-wreath envelope and is therefore hyperlinear.

Assume the explicit finitely presented carrier `W` is hyperlinear and take
canonical normalized-HS microstates.  Packet exactification supplies the
regular `S_9` type and its adjoint Reynolds gap.  Wall placement produces

```text
W_n<=Q_n,     W_n perpendicular P_n,
tr_ad(W_n)>=1/192-o(1).
```

Property `(T)` positive-density commutant no-growth gives instead
`tr_ad(Q_n(I-P_n))<=C delta_n`.  Since `delta_n->0`, these inequalities
contradict one another.  Hence `W` is non-hyperlinear.
