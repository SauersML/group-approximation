---
rg: 2
id: weighted-unitary-hall-deficit-gap-proof
kind: route
title: A target subspace cannot receive more unitary mass than its dimension
target: weighted-unitary-hall-deficit-gap
requires: []
---

Because `U` is unitary,

```text
||U P_S||_2^2=tr_D(P_S).                              (HP1)
```

The two target projections `Q_N` and `1-Q_N` are orthogonal, so Pythagoras
gives

```text
||(1-Q_N) U P_S||_2^2
 =tr_D(P_S)-||Q_N U P_S||_2^2.                       (HP2)
```

The operator `Q_N U P_S` has operator norm at most one and range contained in
`Q_N C^D`.  Hence all its singular values are at most one and there are at
most `rank(Q_N)` nonzero singular values.  Therefore

```text
||Q_N U P_S||_2^2 <= rank(Q_N)/D=tr_D(Q_N).          (HP3)
```

Substituting `(HP3)` into `(HP2)` proves `(HALL1)`.

If `N=N(S)` is the allowed neighbor set, then `(1-Q_N)UP_S` is exactly the
orthogonal sum of the forbidden blocks `Q_j U P_i` with `i in S` and
`j notin N`.  Thus its squared Hilbert--Schmidt norm is their total squared
energy.  A positive weighted Hall deficit supplies the same positive lower
bound, proving the support-graph statement.