---
rg: 2
id: center-chain-mixed-hecke-polars-have-exact-overlap
kind: claim
title: The two mixed center-chain Hecke polars have exact relative cross-Gram mass one over 128
artifacts:
  - research/center-chain-mixed-hecke-range-intersection-proof.md
distinct_from:
  center-chain-mixed-hecke-polars-share-a1-tail: that computes each mixed polar and its individual support; this computes the mutual overlap of their range projections.
  center-chain-mixed-hecke-tail-quantitative-typing: that must still identify the polar maps with the two native selector rows and control the Pauli gauge; this settles only the scalar cross-Gram part of that finite-matrix seam.
  fixed-center-chain-hecke-occurrence-is-regularly-impossible: that forbids a complete fixed exact occurrence row; the overlap here is an exact Hecke calculation and makes no native occurrence assertion.
---

Retain the center-chain character atom `e`, the mixed maps

```text
M_1=e(B_2A_1)z_(K_1),       K_1=<d,v,w>,
M_2=e(B_3A_2A_1)z_(K_2),   K_2=<fc,k,v,w,s>,                 (MHO1)
```

from `center-chain-mixed-hecke-polars-share-a1-tail`, where

```text
d=x_82(b_2), v=x_57(a_1), w=x_67(a_1), s=x_68(a_2),
f=x_94(b_3), k=x_92(b_3), c=x_97(b_3a_1).
```

Let `V_i` be the polar part of `M_i` and `P_i=V_iV_i^*` its range
projection.  Then

```text
tau(P_1P_2)=tau(e)/128,                                      (MHO2)
||V_1^*V_2||_2^2=tau(e)/128.                                (MHO3)
```

In particular the two literal-root mixed Hecke polars have a fixed positive
cross-Gram corner.  The value is obtained from the exact signed-subgroup
intersection

```text
L_1 intersect L_2=H<x_67(a_1)>,                              (MHO4)
```

not from a capacity estimate or an arbitrary rectangular completion.

This closes the scalar-overlap portion of the new Hecke route.  It does not
yet close `center-chain-mixed-hecke-tail-quantitative-typing`: one must still
show, on representation-dependent cuts, that these polar maps are the two
native selector transports and that their relative gauge has the required
mixed source-Pauli control.  The regular-trace firewall therefore remains
respected.

DERIVATION
center-chain-mixed-hecke-range-intersection-proof

