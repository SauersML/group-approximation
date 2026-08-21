---
rg: 2
id: marked-hyperoctahedral-table-linear-dimension-breaker
kind: claim
title: A marked hyperoctahedral multiplication table has a linear robust dimension floor
distinct_from:
  marked-clifford-table-exponential-dimension: that uses `N` Pauli pairs and dimension `2^N`; this uses one signed-permutation packet with minimum marked degree `m` and can simultaneously enforce an arbitrary Boolean predicate.
---

Let `f:W_m->U(d)` be an all-pairs normalized-HS `epsilon`-homomorphism with
`epsilon<1/2`.  If

```text
||f(J)-I||_2>42epsilon,                                  (MHB1)
```

then

```text
d>=(1-4epsilon^2)m.                                     (MHB2)
```

If in addition the Gowers--Hatami exactification dimension `d'` satisfies

```text
d'<m(m-2),                                               (MHB3)
```

then the exactified marked sector satisfies every predicate encoded by the
elements `d_x` of
`low-dimensional-hyperoctahedral-packet-groupifies-any-predicate`.

Thus, after a dimension-matched program prints `D`, choosing

```text
m>D/(1-4epsilon^2)                                      (MHB4)
```

makes a separated `D`-dimensional marked table impossible.  Compared with a
Clifford table this requires a larger finite group but eliminates the
nonlinear BCS-to-group predicate backend on the activated low-dimensional
sector.
