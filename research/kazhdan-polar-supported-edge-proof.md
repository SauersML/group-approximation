---
rg: 2
id: kazhdan-polar-supported-edge-proof
kind: route
title: Average an almost intertwiner and polar-round its invariant part
target: kazhdan-polar-rounding-produces-supported-gallery-edges
requires: []
---

On normalized Hilbert--Schmidt space let

```text
rho(g)T=pi_+(g)T pi_-(g)^*.
```

This is a genuine unitary representation.  The unitary `A` is
`eta`-almost invariant, so `(KPR1)` puts it within
`delta=eta/kappa` of the invariant space.  Let `T` be its orthogonal
projection onto that space.  The mean-ergodic description makes `T` a limit
of convex combinations of the unitary orbit of `A`, hence `||T||_op<=1`.

Write `T=B|T|`.  Invariance implies that the two support projections of
`T` reduce the source and target representations and that `B` is an exact
intertwiner.  On `ker(T)`, `T` vanishes while `A` is unitary, so both source
and target kernel traces are at most `delta^2`.  Mirsky's singular-value
inequality gives

```text
||1-|T|||_2 <= ||A-T||_2<=delta.
```

Consequently `||B-T||_2<=delta`, and the triangle inequality gives
`||A-B||_2<=2delta`.

Finally expand

```text
B P_- - P_+ B
 =(B-A)P_- +(A P_- -P_+A)+P_+(A-B).
```

The middle term has norm `(KPR9)`, proving `(KPR10)`.  Summing the two
support deficits and the rounding errors over six edges yields
`(KPR11)--(KPR12)`.
