---
rg: 2
id: finite-character-one-sided-stabilizer-proof
kind: route
title: Saturate the finite-character Hecke intersection norm
target: finite-character-one-sided-stabilizer-is-its-normalizer
requires:
  - finite-character-hecke-intersection-formula
---

Apply the exact Hecke coefficient formula to `qgq`.  The one-sided identity
`qgq=gq` makes its squared norm equal the full source trace `1/|H|`, whereas
the intersection formula gives either zero or
`|H intersect gHg^-1|/|H|^2`.  Equality forces the intersection to have
order `|H|` and the characters to agree there, hence forces equality of the
two finite subgroups and character preservation.  Conjugating the Fourier
sum gives `gqg^-1=q`; the converse is immediate.
