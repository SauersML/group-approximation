---
rg: 2
id: arithmetic-star-packet-hs-plancherel-anchor-proof
kind: route
title: Exactify the canonical S9 character and compute the regular restriction commutants
target: arithmetic-star-packet-hs-plancherel-anchor
requires:
  - arithmetic-star-packet-carrier
  - gowers-hatami-finite-group-hs-stability
artifacts:
  - notes/ARITHMETIC_STAR_PACKET_HYPERLINEAR_AUDIT.md
---

Canonical trace restricts to the regular character on every finite subgroup.
Gowers--Hatami exactification changes dimension by `o(d)` and changes every
fixed packet character by `o(1)`, so the corrected `S_9` representation is a
multiple of the regular representation up to `o(d)` dimensions.

For the marked difference, the quotient of two distinct star transpositions
has order three.  On a regular block, `1-g` has kernel fraction `1/3`, rank
fraction `2/3`, and nonzero singular value `sqrt(3)`, giving mass squared
`2`.

For any subgroup `G<=K`, `r` regular `K` blocks restrict to
`r[K:G]` regular `G` blocks.  The commutant dimension is therefore
`d^2/|G|`.  An `o(d)` exceptional summand changes this by only `o(d^2)`.
Apply the formula to `Q_0<=Q` and subtract.

