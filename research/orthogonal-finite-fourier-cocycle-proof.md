---
rg: 2
id: orthogonal-finite-fourier-cocycle-proof
kind: route
title: Multiply the source-range partial isometries grade by grade
target: orthogonal-finite-fourier-reps-are-orbit-cocycles
requires: []
---

For fixed `a`, set `w_(a,g)=u_g p_(a,g)`.  Its initial and range projections
are respectively

```text
w_(a,g)^* w_(a,g)=p_(a,g),
w_(a,g) w_(a,g)^*=alpha_g(p_(a,g)).                  (OFP1)
```

The two orthogonal partition identities `(OFC1)` therefore make the
`w_(a,g)` orthogonal in both source and range, so their sum `V_a` is unitary.
For `f in B`, each summand carries its source corner of `B` to its range
corner by `alpha_g`; their orthogonal sum normalizes `B`.

Using `p u_h=u_h alpha_(h^(-1))(p)`, multiplication gives

```text
(u_g p_(a,g))(u_h p_(b,h))
 = u_(gh) alpha_(h^(-1))(p_(a,g)) p_(b,h).            (OFP2)
```

For fixed `h`, the first partition in `(OFC1)` shows that the intersections
in `(OFP2)`, as `g` varies, partition `p_(b,h)`.  Different `h` lie under
orthogonal `p_(b,h)`.  Hence all intersections are orthogonal, and uniqueness
of crossed-product Fourier coefficients says `V_aV_b=V_(ab)` exactly when
their coefficient projections satisfy `(OFC3)`.

The canonical crossed-product trace kills every nonidentity Fourier grade,
so `(OFC4)` follows immediately.  If these values equal the regular
character of `Lambda`, the resulting trace-preserving map is isometric for
the GNS `2`-norm and extends injectively to `L(Lambda)`.

Finally, for `(OFC5)` the three initial projections are `p,q,r`, while their
three range projections are `q,p,r`.  Formula `(OFP1)` makes `V` unitary.
The associated piecewise transformation swaps `E` and `gE` and fixes the
complement, so applying it twice is the identity; equivalently `(OFP2)` gives
`V^2=1`.  All three coefficients are nonzero when
`0<mu(E)<1/2`, proving the asserted failure of homogeneous collapse.
