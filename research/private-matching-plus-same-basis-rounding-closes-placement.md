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
  - same-basis-rounding-interface-for-sparse-weyl-sampler
  - sign-safe-unbounded-multibasin-placement
---

The private sampler supplies the same-Hilbert dimension lower bound, the free-
product shift supplies literal constant-area mixed sign relations and exact
marked completeness, and the same-basis interface rounds the X and Z tapes to
the exact additive actions assumed by the sampler.  The combined incidence
can nevertheless close a contour through several same-basis basins, so the
sign-safe multi-basin input is required in addition to the analytic decoder.
`random-private-matching-eliminates-fixed-multibasin-contours` removes every
fixed-radius family of such contours while retaining the sampler gap; the
listed placement hypothesis is only the residual unbounded holonomy/piece
condition.  The recursive-selection input makes the finite vector/sign lists
effective, so no nonconstructive choice remains in the presentation data.
