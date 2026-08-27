---
rg: 2
id: selector-baumslag-finite-field-orbit-proof
kind: route
title: Tensor the selector square-root with Baumslag finite-field orbit models
target: selector-baumslag-orbits-overlap-or-prepay
requires:
  - selector-product-is-a-payload-corner-square-root
  - baumslag-torsion-host-is-a-quadratic-hs-address-register
  - baumslag-binomial-prefix-centralizer
  - baumslag-address-geometric-stationary-profile
  - independent-address-capacity-cannot-drive-selected-atom-growth
---

Choose a degree-`m` element of `F_(2^m)`, with `m` larger than the requested
finite depth, and use the affine permutation representation from the
Baumslag stationary-profile proof.  Linear independence of the first `m`
lamp translations makes their joint character law uniform.  Tensor with a
scalar BCS assignment and its exact Pauli selector.  Compute the raw cuts and
the ordered first-hit cuts, obtaining `(SBO3)--(SBO4)`; the selector product
commutes with the address factor and only exchanges the two Pauli halves.
Use the quadratic Baumslag fillings to bound reordering errors for a fixed
approximate prefix.  Finally apply trace additivity to pairwise orthogonal
unitary translates to obtain `(SBO5)`.
