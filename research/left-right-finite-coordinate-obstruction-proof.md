---
rg: 2
id: left-right-finite-coordinate-obstruction-proof
kind: route
title: Compress inside traced corners and reapply left-right-finite transport
target: left-right-finite-coordinate-obstruction
requires:
  - left-right-finite-kazhdan-transport
  - faithfully-traced-unital-coordinates
artifacts:
  - research/artifacts/left-right-finite-coordinate-obstruction-2026-08-19.md
---

## Why sufficient

Unitary lifting and projection lifting use only the true parts of
`faithfully-traced-unital-coordinates`: faithful traces make each coordinate
finite, nonzero projections have positive trace, and approximate projection
lifts can be rounded by functional calculus.

Suppose first that the image of a central involution `w` is nontrivial.  The
projection `q=(1-rho(w))/2` is nonzero and central for the group image.  Lift
it to nonzero projections `q_n` on an infinite subsequence, compress the
coordinate lifts, and polar-correct in `q_n A_n q_n`.  Give each corner its
renormalized trace

```text
tau_(n,q)(x)=tau_n(x)/tau_n(q_n).
```

Let `e_n=L_(q_n)R_(q_n)`.  The GNS space of the corner is, up to the scalar
normalization of the inner product, `e_n L^2(A_n,tau_n)`.  Left and right
multiplication by corner elements lie in `e_n D_(tau_n)(A_n)e_n`; hence the
corner left-right algebra is a C-star subalgebra of a corner of a finite
algebra and is finite.  Therefore `left-right-finite-kazhdan-transport`
applies after compression.

The transported commutator `u` tends to `1` in the corner 2-norm, hence so
does `u^2`; but `w=u^2` tends to the scalar `-1` in operator norm on this
corner.  Its 2-distance from `1` is exactly `2`, contradiction.

For a finite normal subgroup inside the compression defect, use the
complement of the finite-group averaging projection instead of the negative
spectral projection.  The same corner inheritance and transport argument
makes every element of the finite subgroup 2-close to `1`, while the average
vanishes on the nontrivial-isotypic corner.  This is the matrix finite-normal
argument verbatim with `M_r` replaced by the left-right-finite corner.

For examples: if `A` is commutative then left and right multiplication agree
and `D_tau(A)` is commutative.  If `A` is AF, the commuting left/right
representations integrate to a representation of `A tensor A^op`; AF
nuclearity identifies maximal and minimal tensor products, `A tensor A^op`
is AF, and its image `D_tau(A)` is an AF quotient.  Hence it is finite.
