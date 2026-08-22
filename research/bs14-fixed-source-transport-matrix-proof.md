---
rg: 2
id: bs14-fixed-source-transport-matrix-proof
kind: route
title: Decompose the R-fixed packet sources and compute the three-way incidence determinant
target: bs14-two-exit-typed-transport-is-not-saturated
requires:
  - bs14-unitary-representations-are-periodic-cycle-packets
  - bs14-trivial-boundary-inversion-forces-r-fixed-source
---

In the packet gauge `(BP4)`, the equation `R(x_0,...,x_(m-1))=x` first
forces all coordinates to equal one vector `xi` and then forces `Vxi=xi`.
This proves `(TET1)` and the scalar `v=1` criterion.

One added source line must participate in one cell for each cubic residual,
so recording source type and the two exit types gives `(TET2)--(TET3)`.
For `(TET5)`, subtract the first row from the second and third and expand
along the first column; the remaining determinant is

```text
det([-1 1 0; -1 0 1; 0 1 1])=2.
```

For the saturation witness, write the four cell variables as
`a,b,c,d` in the order `(TET4)`.  The first four family margins give
`b=c=1-a` and `d=a`; the `e^(2)_1` margin gives `a+d=1`, hence all four
variables equal `1/2`.  This proves `(TET6)` and excludes an integer table.

