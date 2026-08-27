---
rg: 2
id: one-core-endpoint-union-is-one-finite-restriction-fiber
kind: claim
title: One exact BS14 core puts its entire endpoint union in one finite restriction fiber
distinct_from:
  bs14-global-atoms-are-moving-congruence-restrictions: that classifies all exact cores by a directed union of moving congruence restriction monoids; this shows that after one finite-dimensional core is fixed, all of its exact endpoints already lie over one canonical finite quotient.
  congruence-endpoint-orbits-are-restriction-ring-fibers: that classifies endpoint orbits after an ambient congruence quotient has been chosen; this proves that the order of the fixed core's unipotent chooses one finite ambient quotient containing every endpoint over that core.
  bounded-period-iwahori-quotients-are-finite: that proves the one-power quotient is finite and hence pointwise stable; this identifies its representation fiber as the complete exact endpoint union for the supplied core.
---

Let

```text
A=<x,r,s | x^2,(xr)^2,(xs^2)^3,(xrs)^3,
             r s r^(-1)=s^4>,
B=<r,s | r s r^(-1)=s^4>.                            (OCF1)
```

Fix an exact finite-dimensional representation `beta:B->U(d)`.  The
finite-dimensional representation theory of `BS(1,4)` makes `beta(s)` have
finite odd order; write

```text
N=ord(beta(s)).                                       (OCF2)
```

Then every exact endpoint `pi:A->U(d)` whose restriction is literally
`beta` factors through the single finite group

```text
A_N=A/<<s^N>>.                                        (OCF3)
```

Conversely every representation of `A_N` restricting to `beta` is such an
endpoint.  Therefore the complete union of exact endpoint orbits over the
fixed core is the one nonnegative restriction fiber

```text
F_beta^(N)={m in N[Irr(A_N)]:res_(A_N)^B(m)=[beta]}.  (OCF4)
```

The group `A_N` is finite, and `(OCF4)` is a finite set because all its
multiplicity vectors have weighted dimension `d`.  Thus there is no hidden
infinite exact endpoint-type space after a coordinate core has been
authenticated: adaptive type selection is a finite choice at that
coordinate.

This does not give a uniform retraction as the cores move.  Their orders
`N` are unbounded even under all exact endpoint relations, and the stability
radius of `A_N`, the size of `(OCF4)`, and the word cost of recognizing a
fiber point may all deteriorate with `N`.  Compressed Weil packets show that
same-dimensional retraction to this finite union is false uniformly, while
restoring one boundary line repairs those packets.  Hence the remaining
flexible theorem is a moving-family relative liftability statement, not an
uncountable or infinite-fiber selection problem at any one coordinate.

