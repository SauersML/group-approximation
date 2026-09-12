---
rg: 2
id: stw84-overlap-mass-gap-proof
kind: route
title: Force global return mass into one Fourier coordinate
target: stw84-bounded-overlap-fourier-gap
requires:
  - stw84-bounded-coordinate-colour-gap
artifacts:
  - research/artifacts/stw84-bounded-overlap-duplication-firewall-2026-08-30.md
---

Put

```text
epsilon=||Lambda_(h,n)-Psi||.
```

Evaluation at the unit of `C^n` gives

```text
||sum_c X_c|| >= ||h||-epsilon=1-epsilon.              (BOD6)
```

The triangle inequality implies that some colour `c` satisfies

```text
||X_c|| >= (1-epsilon)/r.                              (BOD7)
```

By `(BOD3)`, there is an index `i` with

```text
||x_(c,i)|| >= (1-epsilon)/(rM).                       (BOD8)
```

All `x_(a,i)` are positive, so

```text
Psi(e_i)=sum_a x_(a,i) >= x_(c,i)
```

in the C-star order.  Consequently `(BOD8)` and approximation at `e_i`
give

```text
(1-epsilon)/(rM)
 <=||Psi(e_i)||
 <=||Lambda_(h,n)(e_i)||+epsilon
 =1/n+epsilon.                                         (BOD9)
```

Rearranging `(BOD9)` yields `(BOD4)`, and `n>=2rM` gives `(BOD5)`.

If `T_c` is order zero, the positive elements `T_c(e_i)` are pairwise
orthogonal, so

```text
||sum_i T_c(e_i)||=max_i||T_c(e_i)||;
```

thus `(BOD3)` holds with `M=1`.  If the indices split into `M` orthogonal
families, apply this identity to each family and then the triangle
inequality to obtain `(BOD3)`.

Finally, suppose a coordinate is duplicated by scalar weights before an
order-zero return.  The weighted images of distinct minimal projections
remain orthogonal within that colour, so this is still the case `M=1`.
For band or graph constructions, a proper colouring of the support-overlap
graph into `M` classes gives precisely the last clause above.

No covariance, spectral-gap, trace, finite-dimensional representation, or
support-projection argument enters.  The obstruction sees only the scalar
diagonal of the Fourier matrix and therefore survives all coefficient
amplifications.  Its exact boundary is unbounded overlap in the composed
maps `T_c`; an arbitrary c.p. incoming map followed by an order-zero return
can create such overlap and is not covered.
