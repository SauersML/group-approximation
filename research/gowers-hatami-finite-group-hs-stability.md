---
rg: 2
id: gowers-hatami-finite-group-hs-stability
kind: claim
title: All-pairs approximate representations of finite groups flexibly exactify with universal HS constants
artifacts:
  - research/artifacts/gowers-hatami-normalized-hs-source-audit-2026-08-21.md
distinct_from:
  finite-schur-clifford-packet-flexible-hs-exactification: that converts relator defect for one fixed packet into all-pairs defect with a packet-dependent normal-form constant; this is the group-size-independent stability theorem once an all-pairs map is already supplied.
  hs-stability-descends-to-retracts: that concerns stability of a fixed infinite group presentation; this applies uniformly to every finite group but requires a map defined on its complete multiplication table.
---

Let `G` be finite and let `f:G->U(d)` satisfy

```text
||f(gh)-f(g)f(h)||_2 <= epsilon             for all g,h in G,
epsilon<1/16.                                                    (GHS1)
```

There are an integer `m`, a unitary representation `rho:G->U(m)`, and an
isometry `V:C^d->C^m` such that

```text
d <= m <= d/(1-4epsilon^2),
||f(g)-V^*rho(g)V||_2 <= 42epsilon          for every g in G.     (GHS2)
```

The constants are independent of `G` and `d`.  Flexible enlargement is
necessary in normalized Hilbert--Schmidt norm.

The threshold `1/16` is part of the cited all-finite-group formulation; it
must not be weakened to `1/2` in a generic invocation.  In marked Clifford
applications the additional hypothesis

```text
||f(J)-I||_2>42 epsilon
```

automatically implies `epsilon<1/21<1/16`, since two unitaries are at distance
at most two.  Those applications may therefore state the weaker-looking
ambient assumption `epsilon<1/2`, but the implication uses the separated
mark.
