---
rg: 2
id: parity-return-via-positive-density-commutant-copy
kind: route
title: Amplify the parity excess from one vector to a Schur Reynolds range
target: schur-amplified-parity-compressor-hs-return
requires:
  - toeplitz-parity-compressor-candidate
  - parity-twist-copies-the-old-commutant-into-the-excess
  - predicate-rank-jump-forces-adjoint-reynolds-gap
  - property-t-hs-positive-density-commutant-no-growth
  - parity-compressor-old-commutant-has-positive-density
---

On a marked carrier, use `(PCD1)` to obtain a positive-density old
low-commutator subspace.  Right multiplication by the parity implementer
puts an almost orthogonal copy in the compressed low-commutator space by
`(PTC4)--(PTC5)`.  Property-`(T)` no-growth bounds the density of precisely
that excess by the global microstate defect.  Hence a separated mark forces
a fixed defect floor, while vanishing defect forces the central negative
carrier to disappear.

This route addresses the dilution in `macroscopic-projection-is-one-adjoint-direction`:
the witness is no longer the span of `q`, but an `Omega(d^2)` module obtained
by multiplying a positive-density packet Reynolds carrier by `q`.
