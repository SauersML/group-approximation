---
rg: 2
id: finite-field-augmentation-fourier-matrix-proof
kind: route
title: Use all nonzero additive characters and amplify the full affine matrix block
target: finite-translation-augmentation-corner-has-every-matrix-width
requires: []
artifacts:
  - research/artifacts/noncentral-frobenius-negative-rational-matrix-corner-2026-09-08.md
---

Fourier-transform the additive subgroup of the finite field.
Multiplier conjugation sends `f_b` to `f_(b/s)`. The full
augmentation complement is the sum of every nontrivial additive
character projection. Compressing the basis `f_a m_s` retains
exactly the pairs `a,as` which are nonzero. Their products and
stars are the matrix-unit identities, and their diagonal sum is
the full augmentation projection. This proves the whole-corner
isomorphism, including absence of additional finite-type summands.

Euler's theorem gives the desired divisibility of the block size.
Partition its index set into `D` equally sized pieces and sum
parallel matrix units to obtain the displayed unital `M_D`
embedding. Finite Fourier sums give every coefficient explicitly.

Finally the finite subgroup average is the fixed-vector projection
in every Hilbert-space representation. Its augmentation complement
vanishes exactly when that entire subgroup acts trivially. A
faithful Hilbert-space realization of a C-star algebra gives the
same equivalence for C-star representations. No ambient normality
assumption enters this argument.
