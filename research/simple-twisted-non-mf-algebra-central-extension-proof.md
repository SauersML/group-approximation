---
rg: 2
id: simple-twisted-non-mf-algebra-central-extension-proof
kind: route
title: Cut the central minus corner and use simplicity of the integrated twisted representation
target: simple-twisted-non-mf-algebra-central-extension
requires: []
---

Suppose toward a contradiction that

```text
Theta:E -> U(Q),
Q=product_n M_(d_n)(C) / directSum_n M_(d_n)(C),
```

is injective.  Since `z` is a central involution and `Theta(z)!=1`,

```text
p=(1-Theta(z))/2
```

is a nonzero central projection for `Theta(E)`.  For the canonical section
`s(g)=(1,g)`, put

```text
v_g=p Theta(s(g)) p in U(pQp).
```

The cocycle multiplication law in `E` and `Theta(z)p=-p` give exactly

```text
v_g v_h=omega(g,h)v_(gh),       v_g^*=conjugate(omega(g^(-1),g))v_(g^(-1)).
```

The universal property of the full twisted group algebra therefore supplies
a unital star-homomorphism

```text
Phi:C^*(Gamma,omega) -> pQp.                         (STG1)
```

It is nonzero because its unit is `p`.  Simplicity of the source makes
`Phi` injective.

A projection in a norm matrix corona lifts, after changing a lift by a
norm-null sequence, to coordinate projections `p_n`.  Since `p!=0`, their
ranks are positive on an infinite subsequence.  On that subsequence,

```text
pQp -> product_n M_(rank p_n)(C) / directSum_n M_(rank p_n)(C)
```

is the canonical corner identification.  Hence `(STG1)` is an embedding of
`C^*(Gamma,omega)` into a norm matrix corona, contradicting the hypothesis
that this C-star algebra is not MF.  Thus `E` is not operator-MF.

For the firewall, the twisted left regular representation is nonzero and
integrates to a surjection from the full twisted algebra onto the reduced
one.  If the full algebra is simple, its kernel is zero.  The canonical
coefficient-at-identity trace on the reduced twisted algebra is faithful, so
the identified full algebra is tracial and stably finite.  This excludes all
traceless and properly infinite simple non-MF algebras from the criterion.
