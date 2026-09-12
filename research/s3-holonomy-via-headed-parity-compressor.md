---
rg: 2
id: s3-holonomy-via-headed-parity-compressor
kind: route
title: Absorb the three active channels into a Toeplitz S3 head and use parity commutant no-growth
target: s3-three-channel-multiplicity-holonomy
requires:
  - toeplitz-s3-headed-holonomy-compressor
  - affine-s3-endpoint-permutes-active-atoms
  - s3-active-vector-carries-positive-density-multiplicity-algebra
  - s3-headed-compressor-retains-active-density
  - parity-twist-copies-the-old-commutant-into-the-excess
  - property-t-hs-positive-density-commutant-no-growth
---

Adjoin the affine forbidden-point stabilizer to the packet endpoint and
identify that `S_3` with the external head symmetry.  The affine HNN edge has
already transported the complete three-coordinate active vector, while the
finite affine extension permutes those three coordinates and fixes the exit.
The covariance claim places its positive-density invariant multiplicity
algebra in the old compressor low-commutator space.  Because the compressor
kills the external sign under `alpha`, its parity implementer centralizes the
compressed copy and sign-twists the old copy.  Multiplication by that
implementer creates the orthogonal excess required by the parity theorem.

Property `(T)` commutant no-growth charges the excess to HS relator energy.
The one-jump `b=-1` half remains outside the active vector and hence in the
named exit.  Britton embedding and the properly infinite marked
representation supply completeness.  These are the four clauses of the
target.
