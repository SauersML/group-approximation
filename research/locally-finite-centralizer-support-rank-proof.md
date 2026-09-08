---
rg: 2
id: locally-finite-centralizer-support-rank-proof
kind: route
title: Correct each finite lamp and transport its rank-normalized nonabelian corner
target: locally-finite-centralizer-derived-subgroup-is-mf-invisible
requires: []
artifacts:
  - research/artifacts/compression-locally-finite-centralizer-criterion-2026-09-08.md
---

Sections 1--4 of the artifact give a direct proof from the displayed
hypotheses, including the property-`(T)` assumption in the target.
For Hilbert-space asymptotic representations, the Kazhdan gap gives
a low-energy spectral projection with uniformly vanishing generator
displacements. One-sided compression almost preserves its range in
one direction. Equality of the two off-diagonal block norms of a
finite-dimensional unitary reverses the inclusion.

Correct the restriction to a fixed finite `F<=C` in the original
matrix size, using the regular dilation, averaged range projection,
and polar isometry proved in the artifact. Let `p` be the complement
of the fixed projection for `[F,F]`, of rank `r`. The operators
`rho(c)p` have Hilbert--Schmidt norm `sqrt(r)`. Their actual
commutators with the actor have rank at most `2r`; hence their
operator-norm errors become `o(sqrt(r))` in Hilbert--Schmidt norm.
Apply the preceding compression lemma to their normalized vectors
in the conjugation representation.

The commuting-conjugate relation now makes the transported exact
corner representation asymptotically abelian at the same rank
normalization. Telescoping derived-subgroup words makes each of
their images `o(sqrt(r))` from the corner identity. Their exact
finite average is zero by the definition of `p`, contradicting the
identity's norm `sqrt(r)` unless `r=0` eventually. Local finiteness
places the finitely many factors of each element of `[C,C]` inside
one finite `F`. No normality of `C` or uniform exhaustion bound is used.
