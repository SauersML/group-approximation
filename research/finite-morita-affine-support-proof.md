---
rg: 2
id: finite-morita-affine-support-proof
kind: route
title: Induce every marked selector character through the Morita center
target: finite-morita-toricization-cannot-encode-nonaffine-support
requires: []
---

The stipulated composite center isomorphism sends each central coordinate
function to `p_-z_i`; hence `p_-z_i` belongs to the center of
`p_-C*(F)`.  It follows that every `z_i` acts scalarly on every irreducible
representation with `J=-1`.  Morita equivalence bijects these simple blocks
with the points of `R`, and the separating coordinate functions make their
joint scalar-pattern set exactly `R`.

Let `A=<J,z_1,...,z_m>`, an elementary abelian group.  For any character
`chi` of `A` with `chi(J)=-1`, the nonzero representation `Ind_A^F chi`
lies entirely in the marked sector.  Frobenius reciprocity gives an
irreducible constituent whose restriction contains `chi`.  Centrality makes
each `z_i` scalar on that constituent, and the scalar must be `chi(z_i)`.
Thus every compatible character pattern occurs in `R`; conversely, every
marked irreducible pattern restricts to such a character.

The slice `{chi in A-hat:chi(J)=-1}` is an affine hyperplane over `F_2`, and
restriction to the `z_i` coordinates is a linear map.  Its image, which is
exactly `R`, is therefore affine.  Mere scalar compression in a rank-one
corner would not imply the first step; the target explicitly excludes that
weaker reading.
