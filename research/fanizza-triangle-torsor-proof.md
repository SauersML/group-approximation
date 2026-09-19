---
rg: 2
id: fanizza-triangle-torsor-proof
kind: route
title: Prove the torsor criterion and close it with private half-edge gauges
target: fanizza-triangle-two-cell-has-an-intertwiner-torsor-obstruction
requires: []
---

For edge `e:c->d`, let `I_e` be the unitaries intertwining the complete edge
restriction.  Stable letters satisfy the triangle relation
`U_ZR U_DZ=U_DR` exactly iff

```text
I_DR intersects I_ZR I_DZ.
```

Both directions are immediate by reading or supplying the three
implementers.  Nonemptiness of the three torsors separately is insufficient:
two torsors may preserve a balanced involution `Z`, while the third sends
`Z` to an anticommuting involution `X`; products of the first two never lie
in the third.

For the refined Fanizza packet, duplicate gauge shares so each triangle edge
owns a private Pauli tensor factor while the product of each share pair is
the original logical word.  Let the required commuting private resets be
`W_DZ,W_ZR,W_DR`, and choose the logical implementers flat.  On private
factors set

```text
U_DZ=W_DZ W_DR,
U_ZR=W_ZR,
U_DR=W_ZR W_DZ W_DR.
```

Extra actions occur only on factors invisible to the corresponding edge
group.  Hence all edge covariance laws hold and
`U_ZR U_DZ=U_DR` exactly.  A finite support-adaptive packet menu extends the
nonzero spectral support of the countably amplified HALT representation, so
zero-weight atoms cause no obstruction.  This proves exact developability
for the refined packet, without asserting any matrix Gram estimate.
