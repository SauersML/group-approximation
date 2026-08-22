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
---

The private sampler supplies the same-Hilbert dimension lower bound, the free-
product shift supplies literal constant-area mixed sign relations and exact
marked completeness, and the same-basis interface rounds the X and Z tapes to
the exact additive actions assumed by the sampler.  Since the mixed graph is
a matching, no threshold rectangle, equality-synchronized lift, relative
piece, or balanced-Greendlinger hypothesis remains.  These four inputs give
all clauses of the occurrence compiler and hence the target placement.  The
recursive-selection input makes the finite vector/sign lists effective, so
no nonconstructive choice remains in the presentation data.
