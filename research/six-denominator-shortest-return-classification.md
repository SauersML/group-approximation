---
rg: 2
id: six-denominator-shortest-return-classification
kind: route
title: Solve the root-weight equation and read the relative diagonal word
target: shortest-second-denominator-return-has-coweight-holonomy
requires:
  - first-root-parahoric-target-has-a-distinct-double-coset-type
  - affine-weyl-folner-cut-survives-native-parahoric-triangle
---

Conjugation by the signed Weyl word `s_23` sends the target root
`x_13(2)` to `x_12(plusOrMinus 2)`.  For a diagonal coweight `lambda`, the
`12` root parameter is multiplied by `2^(lambda_1-lambda_2)`.  Inspecting
the six permutations of `(1,0,-1)` shows that exponent `-1` occurs exactly
for `(-1,0,1)` and `(0,1,-1)`, giving `(SDR4)--(SDR6)`.

The two diagonal matrices commute, so their target-side relative word is
`h_1h=diag(2,2,1/4)`.  Equality of its first two entries proves root
centrality, while nontriviality proves that the loop has not returned the
carrier.  Finally it is one fixed translation of the `A_2` coweight lattice,
so the boundary estimate for the Weyl-invariant torus hexagons proves
`(SDR9)`.

