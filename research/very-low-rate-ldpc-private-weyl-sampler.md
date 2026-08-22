---
rg: 2
id: very-low-rate-ldpc-private-weyl-sampler
kind: claim
title: Build the private Weyl sampler from very-low-rate LDPC coordinate functionals
distinct_from:
  independent-private-labels-have-growing-dual-distance: that rules out local checks for independently selected labels; this redesigns the label distribution by starting from a sparse kernel.
  positive-rate-tanner-tests-have-contextual-models: that rules out positive-rate operator agreement; this has length Theta(r squared), dimension r, and adds a full exterior-square overlay.
---

OPEN.  Construct two binary bounded-row/column-weight parity-check systems
of length `K=Theta(r^2)` and nullity exactly `r` such that, after identifying
their coordinate functionals with

```text
a_t,b_t in F_2^r,
```

a pairing of the coordinates has the matrix-valued private Weyl energy gap
of `private-random-weyl-sampler-forces-growing-matrix-dimension`.

Add a degree-one disjoint commutation overlay satisfying
`disjoint-private-pairs-expand-the-full-exterior-square` separately on both
codes.  Prove that every near-perfect tracial reflection representation of
the resulting bounded-local system rounds on the same Hilbert space to its
scalar kernel PVM with a dimension-independent modulus.

The scalar and class-two counts are feasible: sparse checks define the
character code in linear size, nullity `r=Theta(sqrt K)` lies exactly at the
exterior-square threshold, and the degree-one overlay kills that entire
layer.  The unresolved tasks are (i) a sparse-kernel ensemble whose coordinate
functionals retain the Weyl metric-entropy gap, and (ii) exclusion/stability
of the genuinely nonnilpotent contextual quotient left after class two.

A concrete ensemble to test is a bounded-degree sparse invertible matrix
with `r` rows deleted.  Its kernel has dimension `r`, while the relevant
coordinate functionals are rows of the inverse restricted to the deleted
syndrome coordinates.  What is missing is a theorem that these inverse
coordinates have sufficient pseudorandom pair energy together with an
operator agreement theorem for the resulting local views.
