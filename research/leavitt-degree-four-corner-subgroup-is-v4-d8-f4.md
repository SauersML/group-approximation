---
rg: 2
id: leavitt-degree-four-corner-subgroup-is-v4-d8-f4
kind: claim
title: The eight revised degree-four corners generate exactly V4 free-product D8 free-product F4
artifacts:
  - research/leavitt-degree-four-corner-nielsen-proof.md
  - research/artifacts/verify-leavitt-degree4-corner-nielsen.py
distinct_from:
  leavitt-corner-subgroup-is-v4-v4-f2: that is the six-corner subgroup for the earlier two-copy three-gate candidate.
  leavitt-degree-four-one-copy-picture-has-area-at-least-eight: that is a bounded picture census; this is an arbitrary-word normal-form theorem.
---

Let `C=G_0*G_1*G_2*G_3`, with each `G_i` a copy of the Leavitt elementary
group.  The eight cyclic coefficient corners of the four degree-four
Reidemeister--Schreier relators generate

```text
Q = V4(a0,b0) * D8(c3,d3) * F(H,K,L,M),
```

and the displayed map `Q -> C` is injective.  Consequently every identity
among coefficient-region corners of arbitrary length is already a consequence
of the source commutation `[a0,b0]=1`, the exact order-four target product
`c3d3`, the packet involutions, and free reduction.  There is no hidden
long Leavitt relation among the corners.
