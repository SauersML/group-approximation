---
rg: 2
id: opnorm-pauli-cross-check-packing-capacity
kind: claim
title: One surviving commutator mark and off-diagonal cross-checks force finite operator-norm packing capacity
distinct_from:
  robust-clifford-capacity-bound: that uses a full approximate Clifford/Pauli table and yields exponential representation-dimension growth; this needs only one same-site commutator check and one directed cross-commutator check per edge, and uses compact metric packing rather than Clifford representation theory.
  summable-reducing-carriers-force-infinite-clifford-capacity: that assembles exact Clifford cells on nested reducing carriers; this is a one-coordinate operator-norm statement with no carrier density or reducing-subspace hypothesis.
  marked-clifford-table-exponential-dimension: that counts full Clifford rank; this derives capacity from pairwise metric separation of a single family of unitaries.
---

Let `J,X_1,...,X_N,Z_1,...,Z_N` be `d x d` unitaries. Fix
`beta>0` and `epsilon>=0` with `2 epsilon < beta`. Assume

```text
||J-I||_op >= beta,                                           (PPC1)
||[X_i,Z_i]-J||_op <= epsilon                 for every i,   (PPC2)
||[X_i,Z_j]-I||_op <= epsilon                 for i!=j.      (PPC3)
```

Then the `Z_i` are pairwise `delta`-separated in operator norm, where

```text
delta := (beta-2 epsilon)/2 > 0.                              (PPC4)
```

Consequently

```text
N <= Pack(U(d), ||.||_op, delta),                             (PPC5)
```

so for each fixed `d,beta,epsilon` only finitely many cells can coexist.
An explicit Euclidean bound is

```text
N <= (1 + 2 sqrt(d)/delta)^(2 d^2).                           (PPC6)
```

In particular, for fixed `beta` and `epsilon<beta/2`, the minimum matrix
dimension capable of supporting `N` such cells tends to infinity with `N`.

No centrality, involutivity, trace lower bound, positive-density carrier, or
full Clifford multiplication table is required. The mark `J` may be an
arbitrary unitary word whose operator-norm distance from the identity is
bounded below.
