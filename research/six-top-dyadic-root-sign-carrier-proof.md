---
rg: 2
id: six-top-dyadic-root-sign-carrier-proof
kind: route
title: Take the all-negative character of the six-dimensional last congruence root layer
target: six-top-dyadic-root-signs-share-weyl-hexagon-carrier
requires: []
---

For off-diagonal matrix units `E_ij`, multiplication at the last congruence
layer gives

```text
(I+2^(a-1)X)(I+2^(a-1)Y)
 =I+2^(a-1)(X+Y) mod 2^a,                              (SDP1)
```

because `2a-2>=a`.  The six off-diagonal matrix units are linearly
independent over `F_2`; hence the elements `u_ij` generate

```text
E=<u_ij:i!=j> isomorphic to (C_2)^6.                    (SDP2)
```

The factors in `(SDC2)` are commuting projections.  Expanding their product,
only the empty subset contributes the identity group element, so the regular
trace gives

```text
tr(D_a)=2^(-6).                                        (SDP3)
```

A signed permutation conjugates `u_ij` to
`u_(w(i),w(j))^(plusOrMinus 1)`.  At the last dyadic layer `u^-1=u`, so both
simple-Weyl words merely permute the six factors of `(SDC2)`.  This proves
Weyl and closed-gallery invariance.

Finally the elementary Steinberg commutator identities give, for distinct
`i,j,k`,

```text
[x_ij(1),x_jk(2^(a-1))]=u_ik,
[x_ij(2^(a-1)),x_jk(1)]=u_ik.                          (SDP4)
```

Since `D_a u_ik=-D_a`, equations `(SDC6)` follow.  All arguments are
unchanged after regular external amplification.



