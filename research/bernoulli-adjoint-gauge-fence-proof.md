---
rg: 2
id: bernoulli-adjoint-gauge-fence-proof
kind: route
title: Embed the Bernoulli almost-invariant vectors as off-diagonal adjoint gauges
target: bernoulli-adjoint-gauges-fence-uniform-wreath-newton
requires:
  - lamp-cartan-inclusion-is-not-rigid
  - finite-image-summit-wreath-relative-h1-vanishes
---

Use the constant vector in the `q`-biased Bernoulli representation.  Its
lamp displacement is computed exactly by the product character expectation
`(1-2q)^m`, while it has no invariant component.  Embed this representation
as the second block of `1 direct_sum pi_q`.  Rank-one off-diagonal operators
identify the original representation with a subrepresentation of the
adjoint Hilbert--Schmidt module.  Since the invariant-vector space is zero,
the chosen off-diagonal operator stays distance one from the commutant, but
its displacement by every fixed generator tends to zero.  This disproves a
uniform all-representation adjoint gauge inequality.  Separate that exact
fence from the still-open finite-dimensional transverse estimate and global
capture condition.
