---
rg: 2
id: native-bs-level-has-strict-square-root-counterpackets
kind: claim
title: The native one-power BS level has strict counterpackets at the square-root scale
distinct_from:
  exact-torsion-frame-has-rank-one-strict-counterpackets: that proves strict same-dimensional separation at prime dimension scale after exact torsion normalization; this places the same packets inside an exact native one-power BS quotient and translates their defect to the level-word parameter.
  bs14-one-power-level-is-a-native-short-commutator: that shortens the moving level row exactly; this shows that the four remaining relative rows can still be strict-counterpacket defective at order K^-1/2.
  fixed-level-bs14-compatible-basin: that needs flexible finite-group repair and permits vanishing relative padding; this refutes only a same-dimensional strengthening and proves the square-root scale is a genuine boundary scale.
---

There are constants `c,C>0` and an unbounded sequence of integers `K` for
which the finite one-power presentation

```text
<x,r,s | x^2,(xr)^2,(xs^2)^3,(xrs)^3,
         r s r^(-1)s^(-4),[r^K,s]>                    (NSQ1)
```

has same-dimensional unitary tuples `(X_K,R_K,S_K)` such that the BS row,
the native level row, the involution row and the inversion row are exact,
the two cubic defects satisfy

```text
max(||(X_K S_K^2)^3-1||_2,
    ||(X_K R_K S_K)^3-1||_2) <= C/sqrt(K),           (NSQ2)
```

but every exact tuple for `(NSQ1)` in the same dimension obeys

```text
max_(g in {x,r,s}) ||g_K-g_exact||_2 >= c.            (NSQ3)
```

Consequently no strict same-dimensional stability radius for this native
presentation can be asymptotically larger than the square-root scale:

```text
delta_K=omega(K^(-1/2))                              (NSQ4)
```

is impossible.  Shortening the power row to `[r^K,s]` does not create a
better strict basin.

This does **not** refute the flexible basin needed by the hyperlinearity
route.  Each counterpacket has a one-dimensional exact completion at cost
`O(K^(-1/2))` in generalized normalized HS distance.  It instead identifies
the missing positive theorem sharply: the four-row/native-level problem must
turn residual energy into `o(d)` padding, rather than round inside the
original dimension.
