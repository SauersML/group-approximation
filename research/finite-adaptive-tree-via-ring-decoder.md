---
rg: 2
id: finite-adaptive-tree-via-ring-decoder
kind: route
title: Decode the finite conditional corner table and read off adaptive escape
target: finite-depth-adaptive-selected-atom-escape-tree
requires:
  - finite-adaptive-selected-atom-ring-tree
  - atlas-steinberg-context-absorption
  - marked-hs-separation-forces-spectral-density
  - hs-finite-adaptive-ring-tree-decoder
---

Use the seed spectral carrier and decode the finitely many equations
`(FAR1)--(FAR2)` as `(HAT1)`.  Polar correction on each fixed source gives
equal source/range trace up to `o(1)`, while the third equation makes the
range orthogonal to the current carrier up to `o(1)`.  The decoded next
carrier reduces the fixed BCS window, so `maximal-forbidden-atom-has-a-named-positive-half`
can be applied at the next node.  Since the tree is finite, all corrections
sum to one dimension-independent `C sqrt(E)` term.  This is `(FAT1)` on
every reached branch.
