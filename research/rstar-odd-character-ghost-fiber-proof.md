---
rg: 2
id: rstar-odd-character-ghost-fiber-proof
kind: route
title: Enumerate odd subset sizes after translating R-star to the Fano plane
target: rstar-odd-character-ghost-fiber-is-eight-sectors
requires:
  - rstar-fano-ghost-affine-hull-criterion
---

Translate every `s in R_*` by the ghost and identify the result with a
nonzero vector of `F_2^3`.  For odd `T`, translation contributes one copy of
the ghost, so `d(T)=g` exactly when the translated vectors xor to zero.

The xor of all seven nonzero vectors is zero.  For odd subset sizes
`1,3,5,7`, zero xor is respectively impossible, equivalent to being a Fano
line, impossible because the complementary two distinct vectors have
nonzero xor, and automatic.  This gives seven plus one bad subsets.

The seven `R_*` words span `F_2^4`, so the xor map from `F_2^7` has rank four
and every fiber has size eight.  Parity of the image equals parity of the
subset size.  The trace and multiplicity statements follow by Fourier
decomposition of the regular representation of `E`; invariance under
`GL(3,2)` gives centrality in the semidirect product.

