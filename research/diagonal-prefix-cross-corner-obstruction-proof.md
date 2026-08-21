---
rg: 2
id: diagonal-prefix-cross-corner-obstruction-proof
kind: route
title: Multiply two rectangular prefix coefficients and test the Steinberg commutator
target: diagonal-leavitt-prefix-transport-cannot-carry-cross-corners
requires: []
---

The Leavitt prefix identities give `t_v s_u=0` for incomparable `u,v`, so
the calculation `(DPC3)` is immediate.  On the other hand
`beta_(u,v)(1)=s_u t_v` is nonzero in the faithful binary-prefix model, so
`beta_(u,v)(1*1)` is nonzero.  Thus `beta_(u,v)` is not multiplicative.

For distinct outer root indices `i,j,k`, the Steinberg relation reads

```text
[x_ij(a),x_jk(b)]=x_ik(ab).                               (1)
```

Under `(DPC4)`, the left side of `(1)` becomes
`x_ik(beta(a)beta(b))=1`, while the intended image of the right side is
`x_ik(beta(ab))`, which is nontrivial already for `a=b=1`.  Hence no rootwise
Steinberg homomorphism can implement the rectangular map.

Finally, a unit which cyclically permutes three orthogonal idempotent corners
cannot be block diagonal with respect to those corners: its permutation
matrix has one nonzero entry from each source corner to a different target
corner.  For the prefix realization these entries are precisely
`s_u t_v`.  Thus cross-corners are intrinsic to the order-three packet, not
an artifact of one elementary factorization.
