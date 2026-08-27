---
rg: 2
id: finite-index-exact-kazhdan-induction-proof
kind: route
title: Induce the exact subgroup representation and round its almost-invariant range projection
target: subgroup-exact-outliers-do-not-exist
requires: []
---

Let the notation be as in the target.  Replacing the finite-index subgroup
by its normal core preserves near-exactness and leaves a fixed finite index.
Induce the exact subgroup representation to `G`, and use the section
isometry `(SE2)`.  The finitely many section multiplication identities give
the intertwining estimate `(SE4)` by relator and subgroup-word telescoping.
Hence the range
projection of the section isometry is almost invariant for the **exact**
conjugation representation of `G` on the induced Hilbert--Schmidt space.

Property `(T)` now applies without any almost-representation loophole: its
Kazhdan estimate puts that projection within `O(delta)` of the commutant of
the induced representation.  Conditional expectation followed by the
spectral cut at `1/2` produces a commuting projection of rank
`dim(H)+o(dim H)`.  The two-projection polar decomposition identifies
all but `o(dim H)` dimensions of the original range with this exact
invariant range.  Conjugating the exact compressed induced representation
back along that partial isometry, and using the original intertwining
estimate, gives flexible normalized-HS correction on the fixed generators.

Every constant depends only on the presentation, the finite section, and a
Kazhdan pair for `G`, never on matrix dimension.  This proves the target.
