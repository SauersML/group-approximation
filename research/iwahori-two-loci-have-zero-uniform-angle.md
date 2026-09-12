---
rg: 2
id: iwahori-two-loci-have-zero-uniform-angle
kind: claim
title: The reflected BS locus and the two-cubic locus have zero uniform Hilbert--Schmidt angle
distinct_from:
  bs14-two-cubic-strict-repair-constants-diverge: That proves divergence of strict repair moduli from the raw cubic residuals; this converts the same boundary family into an explicit failure of metric linear regularity between the two exact loci targeted by alternating projections.
  projective-dihedral-factorization-has-explicit-hs-retraction: That retracts to the reflection/factorization row alone; this proves that even after that retraction the remaining exact BS and simultaneous-cubic loci approach each other with no dimension-uniform intersection angle.
  iwahori-newton-closes-near-sector: That gives Newton closure inside one fixed torsion-multiplicity tube; this rules out a dimension-uniform global basin-capture or alternating-contraction theorem across all packet levels.
---

**ESTABLISHED.**  In square-free coordinates `(X,R,T)`, let `D_d` be the
exact reflected BS locus

```text
R T R^(-1)=T^4,       X^2=1,       X R X=R^(-1),     (IZL1)
```

and let `C_d` be the simultaneous two-cubic locus

```text
(X T)^3=1,                  (X T^2 R)^3=1.            (IZL2)
```

There is no constant `L`, independent of `d`, for the metric linear
regularity estimate

```text
dist(z,D_d intersect C_d)
 <=L (dist(z,D_d)+dist(z,C_d)).                       (IZL3)
```

Indeed, along `d=(p-1)/2`, `p=1 mod 4`, there are points `z_p in D_d` and
points `y_p in C_d` with

```text
||z_p-y_p||_2=O(p^(-1/2)),
dist(z_p,D_d intersect C_d)>=c>0.                     (IZL4)
```

Thus the two exact varieties become asymptotically tangent in the normalized
Hilbert--Schmidt metric while their intersection remains macroscopically far
in the same dimension.  The explicit projective-dihedral retraction cannot
change this conclusion: the enemy already satisfies its reflection row
exactly.

Consequently no same-dimensional alternating-projection scheme can have,
uniformly in packet level, both a linear movement bound and a contraction
factor bounded below one on every sufficiently small-defect input.  Likewise,
a Newton theorem may be uniform inside an authenticated local tube, but no
dimension-independent residual threshold can by itself capture all small
Iwahori-defect tuples into such a same-dimensional basin.

This does not obstruct flexible repair.  Adding the deleted one-dimensional
Weil line places `z_p` in an exact intersection at relative cost `1/d`.
Accordingly the remaining positive gate is a flexible cross-packet boundary
reconciliation theorem, not a better strict angle estimate.

DERIVATION
iwahori-zero-uniform-angle-from-weil-boundary-proof
