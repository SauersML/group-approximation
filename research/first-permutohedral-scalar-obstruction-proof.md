---
rg: 2
id: first-permutohedral-scalar-obstruction-proof
kind: route
title: Cancel disk faces through free edges and multiply the boundary equations on the S4 sphere
target: first-permutohedral-scalar-obstruction-is-rank-three
requires: []
---

For a single face, choose one boundary edge and set its phase to the inverse
of the prescribed curvature.  For a free-edge face in a larger complex, do
the same and remove that face and edge.  Reverse induction proves flatness
for every free-face collapsible complex, including one hexagon and two
hexagons glued along one edge.

On a closed oriented surface, multiply `(PSC1)` over all faces.  Every edge
appears in exactly two face boundaries with opposite orientation, so its two
factors cancel.  The product is therefore `1` for every edge cochain, which
proves `(PSC2)`.

The Cayley two-complex of `S_3` on its two adjacent transpositions is one
filled braid hexagon.  The rank-three permutohedron for `S_4` is the
truncated octahedron; its boundary is a two-sphere with eight hexagonal
braid faces and six square commuting faces.  Applying `(PSC2)` and setting
the square curvatures to one gives `(PSC3)`.
