---
rg: 2
id: s3-active-vector-carries-positive-density-multiplicity-algebra
kind: claim
title: The three equal-scale S3 active atoms carry a positive-density endpoint multiplicity algebra
distinct_from:
  macroscopic-projection-is-one-adjoint-direction: that shows one large projection still spans only one adjoint vector; this uses every operator on the three external multiplicity spaces and obtains quadratic density.
  predicate-rank-jump-forces-adjoint-reynolds-gap: that compares the full and child Reynolds projections of a generic Schur packet; this computes the density directly on the three S3 active coordinates.
---

Let the three active atom ranks inside an ambient space of dimension `d` be
`r_1,r_2,r_3`, and put

```text
a=(r_1+r_2+r_3)/d=tau(A).                               (SAD1)
```

The endpoint algebra `D=<J,K,b>` acts scalarly on each atom.  Its commutant
therefore contains

```text
M_(r_1)(C) direct_sum M_(r_2)(C) direct_sum M_(r_3)(C). (SAD2)
```

Consequently its normalized adjoint dimension is at least

```text
(r_1^2+r_2^2+r_3^2)/d^2 >= a^2/3.                      (SAD3)
```

Thus any fixed positive active Hilbert mass supplies a dimension-independent
positive-density family of multiplicity operators.  No rank integrality or
single-vector estimate is used.  After fixed-packet flexible exactification,
the same lower bound holds with an `O(sqrt(E))` loss in the carrier mass.

For the holonomy program this removes the density-generation problem at the
endpoint level.  The remaining coefficient-covariance theorem must make the
compressor act through the endpoint algebra on `(SAD2)`—not through an
uncontrolled residual action—and must visibly exclude the tensor-decoupled
representation.
