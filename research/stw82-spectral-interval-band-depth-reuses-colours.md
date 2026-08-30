---
rg: 2
id: stw82-spectral-interval-band-depth-reuses-colours
kind: claim
title: Spectral interval band depth bounds the needed global order-zero colours
distinct_from:
  stw82-indivisible-order-zero-reuse-is-graph-colouring: that computes colours from every pairwise support product; this supplies a directly checkable spectral-band hypothesis whose interval geometry bounds that chromatic number.
  stw82-raw-two-cut-reuse-iff-quasidiagonal: that requires the complementary cuts themselves to become projectional; this permits genuinely overlapping nonprojectional bands and controls only their overlap multiplicity.
---

Let `h` be a positive contraction in a C*-algebra `B`.  For a finite set
`V`, let

```text
phi_v:F_v -> B
```

be cpc order-zero maps from unital C*-algebras.  Suppose that for every
`v` there are a positive continuous function `f_v` on `[0,1]` and a closed
interval `J_v subset [0,1]` such that

```text
phi_v(1)=f_v(h),
f_v(t)=0 for t notin J_v.                              (B1)
```

If the interval family has depth at most `d`, meaning

```text
sup_(t in [0,1]) |{v:t in J_v}| <= d,                 (B2)
```

then the maps `(phi_v)` can be partitioned into `d` classes so that the
direct sum over every class is cpc order zero.

Consequently, if a C*-algebra `A` has arbitrarily accurate
finite-dimensional approximations whose constituent outgoing order-zero
maps satisfy (B1)--(B2) with `d=r+1`, then

```text
dim_nuc(A) <= r.                                      (B3)
```

This is exact nonprojectional colour reuse: the functions `f_v` and their
bands may overlap, and no perturbation to projections is assumed.  The
assertion is a sufficient theorem for spectrally banded approximations, not
a claim that arbitrary extension approximations admit such a banding.
