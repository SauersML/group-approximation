---
rg: 2
id: twisted-c-star-opposite-inverts-cocycle-proof
kind: route
title: Take adjoints of the projective generators and opposite every local lift
target: twisted-c-star-opposite-inverts-cocycle
requires: []
---

Let `u_g` denote the canonical generators of `C^*(G,alpha)`, so

```text
u_g u_h = alpha(g,h) u_(gh).
```

Inside the opposite algebra put `v_g=(u_g^*)^op`.  Multiplication reverses,
and therefore

```text
v_g v_h
 = (u_h^* u_g^*)^op
 = ((u_g u_h)^*)^op
 = conj(alpha(g,h)) v_(gh).                            (TOP2)
```

The `v_g` generate the opposite algebra.  The universal properties in both
directions now give `(TOP1)` as a star isomorphism.

For completeness, LLP is invariant under taking opposites.  A ucp map
`A^op -> B/J` is, after taking opposites, a ucp map

```text
A -> (B/J)^op ~= B^op/J^op.
```

Apply LLP for `A` on the opposite of the chosen finite-dimensional operator
system, obtaining a local ucp lift into `B^op`, and take opposites again to
obtain a local ucp lift into `B`.  Reversing the argument proves the converse.
Combining this with `(TOP1)` proves the LLP equivalence.  Finally a
`mu_3`-valued representative satisfies `conj(alpha)=alpha^2` pointwise,
which identifies the two Deligne fibres.
