---
rg: 2
id: finite-support-stabilizer-and-free-square-shadow-proof
kind: route
title: Compare pointwise and normalizer stabilizers of a signed Reynolds atom
target: finite-reynolds-carriers-have-only-finite-pointwise-stabilizer
requires:
  - finite-inclusion-is-free-self-compressor-quotient
  - left-rank-amplification-is-not-a-fixed-sector
  - packet-covariant-kernel-gauge
  - selector-product-is-a-payload-corner-square-root
---

Use the faithful permutation action of the left stabilizer on the finite
support of a group-algebra coefficient to prove `(FRC1)`, and compare supports
of `g e_(K,chi)` and `e_(K,chi)` for `(FRC3)`.  For the calibration, square
both generators of `F_2` and let the parity of one generator exchange the two
coordinates of `C_2^2`; its two asymmetric character atoms are orthogonal.
Form the ascending HNN extension and tensor the atom with a forbidden BCS
selector projection.  Finally apply the packet-covariant Schur form to show
that normalizer covariance leaves the full kernel multiplicity gauge and
therefore does not create a pointwise-fixed adjoint sector.
