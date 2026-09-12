---
rg: 2
id: stw81-first-high-dimensional-composition-step-proof
kind: route
title: Stop at the first composition-series step of nuclear dimension at least two
target: stw81-finite-ideal-counterexample-forces-lxxxii-counterexample
requires: []
---

A finite ideal lattice admits a finite composition series

```text
0=J_0 properSubset J_1 properSubset ... properSubset J_m=A
```

whose factors `Q_j=J_j/J_(j-1)` are simple.  Nuclear dimension passes to
ideals and quotients, so every `J_j` and `Q_j` has finite nuclear dimension.

Each simple factor has nuclear dimension at most one.  An elementary factor
has nuclear dimension zero.  A non-elementary factor is simple, separable,
nuclear, and has finite nuclear dimension, so the simple structure theorem
gives nuclear dimension one (or zero in the AF case).  Notice that this
conclusion does not require the commutative-shadow hypothesis; finite nuclear
dimension and simplicity already force the zero/one dichotomy for the
composition factors.

Since `dim_nuc(J_0)=0` while `dim_nuc(J_m)>=2`, choose the least `j` for
which `dim_nuc(J_j)>=2`.  Then

```text
dim_nuc(J_(j-1)) <= 1,
dim_nuc(Q_j) <= 1,
dim_nuc(J_j) >= 2.
```

The exact sequence

```text
0 -> J_(j-1) -> J_j -> Q_j -> 0
```

is therefore a counterexample to the LXXXII maximum formula, and all three
algebras are subquotients of `A`.  This proves the asserted internal
localization.
