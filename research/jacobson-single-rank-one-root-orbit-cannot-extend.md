---
rg: 2
id: jacobson-single-rank-one-root-orbit-cannot-extend
kind: claim
title: A single rank-one root orbit cannot extend to the Jacobson boundary presentation even with arbitrary root-trivial summands
distinct_from:
  jacobson-mixed-cells-reconstruct-full-first-level-root-packet: that reconstructs the finite matrix root subgroup; this excludes its smallest nontrivial character sector in every representation of the full presentation.
  binary-jacobson-gl3-k-branching-has-regular-counterprofile: that gives consistent branching counts before the additional boundary and TS relations; this uses two reconstructed packets and their shared subgroup to exclude one specified support profile.
artifacts:
  - research/artifacts/jacobson-single-rank-one-orbit-obstruction-2026-09-08.md
  - research/artifacts/jacobson-first-root-packet-dimension-audit-2026-09-08.md
  - research/artifacts/jacobson-first-root-packet-coherent-rounding-2026-09-08.md
---

Let `Xi` and `N=Mat_(3 x 3)(F_2)_add` be as in
`jacobson-mixed-cells-reconstruct-full-first-level-root-packet`.
There is no finite-dimensional unitary representation of `Xi` whose
nontrivial `N`-character support consists of exactly the rank-one orbit
with one-dimensional character spaces. An arbitrary `N`-trivial
complement is allowed in this assertion.

Consequently every exact finite-dimensional representation retaining
the head mark has dimension at least 98. For exact compatible
representations of the finite factors `F,J` in dimensions at most 97,
retaining the head mark, the maximum of the TS and first-braid errors
has a strictly positive lower bound.

Coherent finite-packet correction gives the explicit lower bound

```text
max(||W-I||,||(Hb)^3-I||) >= 1/(8192*2,228,976)
```

on these dimensions. After correction, the single-orbit contradiction
needs only first-braid defect less than two: this forces the same
involution multiplicities as an exact braid. The packet relations used
by the rest of the argument are exact. Neither this bound nor the
support obstruction settles `jacobson-boundary-amalgam-mixed-gap`,
whose infimum ranges over all dimensions.

DERIVATION
jacobson-root-orbit-shared-multiplicity-proof
