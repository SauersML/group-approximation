---
rg: 2
id: uniform-infinite-pauli-packing-impossible
kind: claim
title: A finite matrix algebra cannot contain an infinite uniformly anticommuting family
distinct_from:
  projective-holonomy-rank-forces-exponential-multiplicity: that gives an exponential divisor from a finite projective cocycle rank; this uses compactness to rule out an actually infinite coherent family at any fixed error below two, without estimating its finite packing number.
  infinite-index-does-not-force-supercritical-site-rank: that shows recovery of every external finite window is compatible with exact finite truncations; this requires all infinitely many sites to coexist coherently in one candidate matrix model.
---

Let `0<=epsilon<2`.  There are no `d<infinity` and no infinite family of
unitaries `(A_i)_(i in I)` in `M_d(C)` satisfying

```text
||A_i A_j + A_j A_i||_2 <= epsilon       for every i!=j.          (UIP1)
```

No dimension bound or rate is required.  In particular, if a fixed finite
presentation and a dimension-independent rounding theorem turn every
sufficiently accurate marked microstate into one coherent infinite family
with `(UIP1)`, that presentation already has a uniform normalized-HS energy
floor.  One need not choose a finite rank larger than the logarithm of the
matrix dimension.

The word **coherent** is essential.  Producing an exact copy of every fixed
finite Pauli window in a different correction, corner, or representation does
not put an infinite family in one `M_d(C)` and is compatible with
`infinite-index-does-not-force-supercritical-site-rank`.

There is also an explicit finite packing bound.  Put

```text
rho=1-epsilon/2>0.
```

Every finite family satisfying `(UIP1)` has

```text
|I| <= (1+2/rho)^(2d^2).                                        (UIP2)
```

Thus a finite-word coherence theorem could replace the infinite conclusion
by recovery of more than the right side of `(UIP2)`.  This threshold is much
larger than the logarithmic threshold supplied by exact projective cocycle
rank, so `(UIP2)` is mainly useful when coherence is naturally orbit-wide.
