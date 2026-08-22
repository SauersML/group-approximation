---
rg: 2
id: private-matching-plus-same-basis-rounding-closes-placement
kind: route
title: Combine private free-product signs with one same-basis additive decoder
target: colored-cayley-pauli-incidence-separation
requires:
  - private-random-weyl-sampler-forces-growing-matrix-dimension
  - private-matching-free-product-separates-pauli-signs
  - private-weyl-samplers-admit-recursive-selection
  - cayley-module-bilinear-certificate-protects-pauli-mark
  - same-basis-rounding-interface-for-sparse-weyl-sampler
  - sign-safe-unbounded-multibasin-placement
---

The private sampler supplies the bounded-flexible dimension lower bound, the free-
product shift supplies literal constant-area mixed sign relations and exact
marked completeness, and the same-basis interface rounds the X and Z tapes to
exact additive actions of dimension at most a fixed multiple of the original
matrix dimension.  The strengthened sampler absorbs that multiple.  The combined incidence
can nevertheless close a contour through several same-basis basins, so the
sign-safe multi-basin input is required in addition to the analytic decoder.
`random-private-matching-eliminates-fixed-multibasin-contours` removes every
fixed-radius family of such contours while retaining the sampler gap; the
listed placement hypothesis is only the residual exact invariant-pairing
extension across all same-basis relation orbits.  The recursive-selection
input makes the finite vector/sign lists effective, so no nonconstructive
choice remains in the presentation data.

The residual placement input now has an exact algebraic formulation.
`cayley-module-bilinear-certificate-protects-pauli-mark` shows that it is
enough to realize the same-basis faces as finite-orbit relation submodules
`R_X,R_Z` over one address group and separate the prescribed mixed prototype
tensors in `(M_X tensor M_Z)_A`.  Once that coinvariant separation is proved,
the explicit translation/phase model excludes all long contour collapses at
once; no separate relative small-cancellation estimate is needed.
