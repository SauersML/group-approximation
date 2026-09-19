---
rg: 2
id: rational-supercritical-branch-certificate
kind: claim
title: A rational positive subeigenvector certifies supercritical branch pressure
artifacts:
  - experiments/branching_pf_certificate.py
---

Let `A` be a finite nonnegative integer branch-incidence matrix and suppose
nonnegative vectors `x,e` satisfy

```text
x >= A x - e.                                         (RBC1)
```

If there are a positive rational vector `y` and a positive rational number
`kappa` such that

```text
A^T y >= (1+kappa) y,                                (RBC2)
```

then

```text
kappa (y . x) <= y . e.                              (RBC3)
```

Thus no computation with algebraic Perron eigenvalues is needed in a finite
branching obstruction.  The exact finite certificate consists only of the
integer matrix `A` and rational numbers `y,kappa`; checking it is finite
integer/rational arithmetic.  `experiments/branching_pf_certificate.py` uses
floating point only to propose `y` and then verifies `(RBC2)` exactly with
`fractions.Fraction`.

For the doubled two-cycle

```text
A = [[0,1],
     [2,0]],
```

the checker finds such a certificate, whereas the neutral two-cycle with the
lower-left `2` replaced by `1` correctly has none.  This makes the new atlas
branch-automaton search proof-carrying: every positive result can be committed
as a small rational certificate and checked independently of the search
heuristic.