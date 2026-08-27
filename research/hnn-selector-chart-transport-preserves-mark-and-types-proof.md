---
rg: 2
id: hnn-selector-chart-transport-preserves-mark-and-types-proof
kind: route
title: Apply HNN normal form and align the two finite abelian restrictions
target: hnn-selector-chart-transport-preserves-mark-and-types
requires:
  - finite-group-shared-overlap-polar-alignment
  - shared-overlap-controls-packet-multiplicity-vector
---

Britton normal form embeds the base `G` in `(HST1)`, proving marked
completeness. Exact evaluation of the stable-letter relations gives unitary
equivalence between `rho|D_0` and `rho|D_1 o theta`, so their character
multiplicities agree. No relation says elements of `D_0` commute with elements
of `D_1`.

For an approximate tuple, exactify the two fixed elementary-abelian tables.
The evaluated stable letter approximately intertwines them, with error bounded
by the finite relation list. Average/polar-align that approximate intertwiner.
The shared-overlap type-vector theorem bounds the weighted unmatched
multiplicity by the discarded corners, giving `C sqrt(E)`. The table and
isomorphism are fixed, so the constant is dimension independent.

