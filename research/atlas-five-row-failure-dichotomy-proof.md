---
rg: 2
id: atlas-five-row-failure-dichotomy-proof
kind: route
title: Split a vanishing best-constant sequence by additive energy
target: atlas-five-row-lift-failure-dichotomy
requires: []
---

Write `A_k,B_k` for the nonnegative energies in `(FPG1)`.  The uniform
five-row estimate fails exactly when there are `k_n,U_n` with

```text
A_(k_n)(U_n)>0,
B_(k_n)(U_n)/A_(k_n)(U_n) -> 0.                       (AFD1)
```

Each of the five rows is a fixed finite sum of unitaries, so `A_k(U)` is
bounded above by a constant independent of `k,U`.  Pass to a subsequence on
which `A_(k_n)(U_n)->a>=0`.

If `a>0`, `(AFD1)` forces `B_(k_n)(U_n)->0`.  Word evaluation and the five
row quadratic forms pass to the tracial matrix ultraproduct, yielding the
macroscopic exact six-relator solution with positive additive energy.

If `a=0`, put `eta_n=sqrt(A_(k_n)(U_n))`.  The normalized five-row vector

```text
Xi_n=(rho(z_j)U_n/eta_n)_j
```

has squared Hilbert norm one.  Since `B_k` is a sum of six nonnegative
squared residuals, `(AFD1)` says that every residual divided by `eta_n`
tends to zero.  This is precisely the normalized blow-up alternative.

The alternatives are disjoint because their additive energies tend to a
positive number and to zero, respectively.  This proves the stated
compactness dichotomy and the best-constant equivalence.
