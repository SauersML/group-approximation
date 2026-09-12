---
rg: 2
id: two-site-a5-plancherel-center-proof
kind: route
title: Exactify the two A5 factors and evaluate the rational five-dimensional central type
target: two-site-a5-plancherel-center-separates-mark
requires:
  - gowers-hatami-finite-group-hs-stability
---

Canonical trace restricts to the regular character on the fixed finite
subgroup `L=A5_p x A5_q`.  Finite-group Hilbert--Schmidt exactification
therefore changes the microstate by `o(1)` and leaves, up to `o(d)`
dimensions, Plancherel multiplicities for `L`.

For a finite group, the central idempotent of an irreducible representation
of degree `r` has normalized regular trace `r^2/|K|`.  The rational
five-dimensional irreducible of `A5` therefore has mass

```text
5^2/|A5|=25/60=5/12.
```

The two coordinate types are independent in the regular representation of
the direct product, so their intersection has mass `(5/12)^2=25/144`.
The exclusive-or mass is consequently

```text
2(5/12)(1-5/12)=35/72.
```

Its character has values `5,1,-1,0,0` on the identity, order-two,
order-three, and two order-five classes.  The standard central-idempotent
formula therefore gives

```text
z=(5/60)(5*1+C_2-C_3)=(1/12)(5*1+C_2-C_3).
```

This is a fixed rational sum of 36 group elements.  Conjugation covariance
of each term telescopes through the expression.  Exactification changes it
by `o(1)`, proving the finite-list covariance statement `(TAP4)`.
