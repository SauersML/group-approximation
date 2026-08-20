---
rg: 2
id: gowers-hatami-finite-group-hs-stability
kind: claim
title: All-pairs approximate representations of finite groups flexibly exactify with universal HS constants
distinct_from:
  finite-schur-clifford-packet-flexible-hs-exactification: that converts relator defect for one fixed packet into all-pairs defect with a packet-dependent normal-form constant; this is the group-size-independent stability theorem once an all-pairs map is already supplied.
  hs-stability-descends-to-retracts: that concerns stability of a fixed infinite group presentation; this applies uniformly to every finite group but requires a map defined on its complete multiplication table.
---

Let `G` be finite and let `f:G->U(d)` satisfy

```text
||f(gh)-f(g)f(h)||_2 <= epsilon             for all g,h in G,
epsilon<1/2.                                                     (GHS1)
```

There are an integer `m`, a unitary representation `rho:G->U(m)`, and an
isometry `V:C^d->C^m` such that

```text
d <= m <= d/(1-4epsilon^2),
||f(g)-V^*rho(g)V||_2 <= 42epsilon          for every g in G.     (GHS2)
```

The constants are independent of `G` and `d`.  Flexible enlargement is
necessary in normalized Hilbert--Schmidt norm.

