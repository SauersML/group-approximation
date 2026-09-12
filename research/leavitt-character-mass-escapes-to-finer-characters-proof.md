---
rg: 2
id: leavitt-character-mass-escapes-to-finer-characters-proof
kind: route
title: Exhibit the diffuse CAR limit in which the doubling relation is harmless
target: leavitt-character-mass-escapes-to-finer-characters
requires: []
artifacts:
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
---

## Direct proof

The finite-dimensional argument uses exactly one compactness step: the
character set of an exact finite-dimensional representation is finite, so `m`
attains a maximum.  Removing that step is what has to be exhibited.

Take the branch-doubling operation `F` on characters and iterate it along a
sequence of models of growing dimension.  Each application halves the
character mass per character while doubling the number of characters carrying
it, so the total mass is conserved and the support refines.  In the limit the
character distribution is **diffuse**: no character carries positive mass, and
`m` has no maximum.

Such a limit is realized: an infinite CAR/UHF-type representation of the
binary Leavitt relations has exactly this diffuse character behaviour, and in
it `(MD)` holds with no contradiction, because both sides are zero.  So `(MD)`
is consistent with a faithful infinite-dimensional model, which is precisely
the statement that it cannot by itself obstruct a matrix-microstate model.

For the two consequences: the escape is compatible with every relation of the
presentation holding exactly, so no amount of further algebra -- self-copy,
commutator identities, normal generation -- removes it; and a spectral-gap
hypothesis on the character side is exactly a hypothesis that the support does
not refine, i.e. it reintroduces the missing maximum by assumption rather than
proving it.
