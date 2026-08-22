---
rg: 2
id: regular-depth-bands-form-geometric-convolution
kind: route
title: Compute the regular conductor bands and convolve a triangular top-level profile
target: regular-congruence-depth-mixtures-remain-folner
requires:
  - fixed-shift-invariance-does-not-force-flat-profile
---

For a quotient `G_a -> G_b`, an irreducible representation of `G_a` occurs
in the regular representation with multiplicity equal to its dimension.
The sum of `dim(tau)^2` over irreducibles that factor through `G_b` is
therefore `|G_b|`.  Smoothness of `SL_3` over `Z_p` gives a reduction kernel
of order `p^8` at every step, proving `(RDF2)--(RDF3)`.

Integer multiplicities realize every finite rational profile of regular
blocks exactly.  Formula `(RDF3)` then identifies the genuine conductor
profile with convolution by `kappa`, except that its tail below level one is
collapsed into the bottom band.  Convolution by a probability measure is a
contraction in total variation.  The collapsed tail has mass at most
`q^(L-1)`, giving `(RDF5)`.

The triangular profiles have fixed-shift variation `O(|s|/N)` by
`fixed-shift-invariance-does-not-force-flat-profile`; their largest atom is
`O(1/N)`.  Convolution cannot increase either quantity, apart from the
vanishing bottom tail.  This proves `(RDF7)`.

Finally, a nonidentity integral matrix cannot be congruent to the identity
modulo `p^a` for arbitrarily large `a`.  Thus sufficiently deep regular
quotient blocks have trace zero on any prescribed finite set of nonidentity
lattice elements, proving the canonical-character assertion.

