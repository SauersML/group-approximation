---
rg: 2
id: bounded-cycle-coboundary-inverse
kind: claim
title: Mean-zero coboundaries on cycles of length at most K have inverse norm at most K/4
artifacts:
  - research/artifacts/bs14-bounded-cycle-shadowing-2026-08-22.md
distinct_from:
  long-cycles-have-unbounded-l2-coboundary-inverse: that gives the matching linear lower-growth obstruction as the cycle length tends to infinity; this gives the uniform upper bound after a period cap is imposed.
  weyl-defect-koopman-spectral-regularity: that concerns the arithmetic Weyl defect inside a full matrix commutant; this is the exact Fourier estimate on the cyclic coordinate summands only.
---

Let `psi` be a unitary on a finite-dimensional Hilbert space which is an
orthogonal sum of cyclic summands of lengths `L<=K`, with `K>=2`.  Let `E` be
the orthogonal projection onto `ker(1-psi)`.  Then for every vector `x` there
is a unique minimum-norm vector `y` orthogonal to `ker(1-psi)` such that

```text
(1-psi)y=x-Ex,                                         (BCI1)
```

and

```text
||y|| <= [2 sin(pi/K)]^(-1)||x-Ex||
      <= (K/4)||x-Ex||.                                (BCI2)
```

The same estimate holds for the fourth-power coordinate shift on the
commutative spectral algebra of any exact `BS(1,4)` representation whose
fourth-power orbit lengths are at most `K`.  Thus, after bounded-period
truncation, the coordinate coboundary loses at most a linear factor in `K`;
any further obstruction must lie in the fixed component, packet
multiplicity/monodromy, or in transporting the arithmetic defect through the
skeleton perturbation.
