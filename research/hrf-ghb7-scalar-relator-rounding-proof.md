---
rg: 2
id: hrf-ghb7-scalar-relator-rounding-proof
kind: route
title: Compute the degree-two equivariant homology filtration, discretize commutator phases, and correct seventh powers
target: hrf-ghb7-scalar-relator-models-round-strictly
requires:
  - cckw-ghb2-kms-group-structure
  - ghb7-triangle-vertex-groups-split-abelianizations
artifacts:
  - research/artifacts/hyperbolic-rf-ghb7-2026-09-20.md
---

Sections 7-8 of the artifact give full proofs. In the equivariant
integral homology spectral sequence of the contractible triangle
development, E2_(0,2) is the sum of the three vertex H2 groups, since
cyclic edges have H2=0. E2_(1,1)=0 because the two incident edge classes
are independent in each vertex abelianization. E2_(2,0)=0 because the
quotient is a filled triangle. The sole possible higher differential
into E2_(0,2) has source E2_(2,1)=0, since the face stabilizer is
trivial. Thus H2(G) is the vertex sum. Transfer kills each finite
vertex's positive homology by its order, giving exponent dividing 2401.

A scalar-relator tuple defines a character of N/[F,N] for the free
presentation F/N. Hopf's formula puts the eight commutator-relator
classes in H2(G), so their phases are 2401st roots. The stated strict
threshold forces them to equal 1. Near-one scalar seventh roots correct
the three power relators and leave every commutator unchanged. The
elementary sine bound gives the quantitative error. Copy-equality
relators give the doubled version by the triangle inequality.
