---
rg: 2
id: reynolds-rank-gap-forces-hs-holonomy-energy-proof
kind: route
title: Compare projection ranks in adjoint Hilbert space and bound adjoint transport by matrix transport
target: reynolds-rank-gap-forces-hs-holonomy-energy
requires: []
---

Normalize the Hilbert--Schmidt norm on superoperators by the dimension
`d^2` of `L^2(M_d)`. For orthogonal projections `P_0,Q_0`,

```text
||P_0-Q_0||_(2,super)^2
 = (rank(P_0)+rank(Q_0)-2 Tr(P_0Q_0))/d^2
 >= |rank(P_0)-rank(Q_0)|/d^2.                                (RHG3)
```

Indeed `Tr(P_0Q_0)` is at most the smaller rank. Conjugating `P` by the
superunitary `Ad(T)` does not change its rank.

For ordinary unitaries `A,B`, direct evaluation on an orthonormal matrix-unit
basis gives

```text
||Ad(A)-Ad(B)||_(2,super)^2 = 2(1-|tau(A*B)|^2).
```

Since `|1-tau(A*B)|^2>=0`,

```text
1-|tau(A*B)|^2 <= 2(1-Re tau(A*B))=||A-B||_2^2,
```

and consequently

```text
||Ad(A)-Ad(B)||_(2,super)^2 <= 2||A-B||_2^2.                   (RHG4)
```

Now `Ad(T)PAd(T)*-Q` is the average of
`Ad(TU_jT*)-Ad(V_j)`. Jensen's inequality and `(RHG4)` bound its squared
superoperator norm by `2 epsilon`. Combining this with `(RHG3)` proves
`(RHG2)`.

