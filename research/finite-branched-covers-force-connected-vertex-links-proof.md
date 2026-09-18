---
rg: 2
id: finite-branched-covers-force-connected-vertex-links-proof
kind: route
title: Onto link coverings make the image of a branched cover open, closed and full, and a connected link cannot cover a disconnected one
target: finite-branched-covers-force-connected-vertex-links
requires: []
---

Cells and links are as in Bridson--Haefliger I.7 (polygonal cells, glued by
characteristic maps that need not be injective on the boundary).  The link
`Lk(y)` has one vertex for each end of a 1-cell at `y` and one edge for each
corner of a 2-cell at `y`.  Every closed cell has at least one vertex in its
boundary.

## Part 1

Let `X` be nonempty.  Then `X` has a vertex, since every cell has one.

*The image is a union of closed cells.*  `p` maps each closed cell onto a
closed cell, so `Z = p(X)` is a subcomplex.

*`Z` contains the closed star of each of its vertices.*  Let `y in Z` be a
vertex.  Since `p` maps open cells onto open cells and 0-cells to 0-cells,
`y = p(x)` for a vertex `x`.  A cell `sigma` of `Y` incident to `y` gives a
vertex or an edge of `Lk(y)`.  The covering `Lk(x) -> Lk(y)` has degree
`d_x >= 1`, so it is onto, and that vertex or edge is the image of a vertex
or edge of `Lk(x)`.  That is, `sigma` is the image of a cell of `X` incident
to `x`, and `sigma subset Z`.

*`Z` is open.*  Let `z in Z` lie in the open cell `e`.  A neighbourhood of `z`
in `Y` is contained in the union of the closed cells `sigma` whose closure
contains `e`.  Each such `sigma` has a vertex in the closure of `e`, which
lies in `Z`, so `sigma subset Z` by the previous paragraph.

*`p` is onto.*  `Z` is compact, hence closed, open and nonempty in the
connected space `Y`.  So `Z = Y`, and every vertex `y` of `Y` equals `p(x)`
for some vertex `x`.

*Links.*  `Y` is connected and not a point, so every vertex lies on a 1-cell
and `Lk(y)` is nonempty.  `Lk(y)` is the image of the connected graph
`Lk(x)` under a continuous surjection, so it is connected.  QED

## Part 2

*Links of `W`.*  At `c`, each square contributes one corner of angle
`pi/2`, so `Lk(c)` is two disjoint edges of length `pi/2`.  At each of the
other six vertices the link is one edge of length `pi/2`.  No link contains a
cycle, so every link has angular girth `infinity >= 2 pi`.  By the Gromov link
condition for 2-complexes with finitely many shapes (B--H II.5, the form
used in Step 0 of `sparse-branched-covers-sofic-pi1-reduction-proof`) `W` is
locally CAT(0).

*Topology.*  `W` is a wedge of two closed disks, so it is contractible and
`pi_1(W) = 1`.  The trivial group is sofic.

*No branched cover.*  `Lk(c)` is disconnected, so by Part 1 no nonempty finite
branched cover of `W` exists.  QED

## Part 3

Glue a unit square `Q` to `Y_1^2` by identifying one corner of `Q` with a
vertex `y_0`.
* Every cycle in `Lk_(Y')(y_0) = Lk(y_0) ⊔ (one edge)` lies in `Lk(y_0)`.
  The other new links are single edges.  So all angular girths are still at
  least `2 pi`, and `Y'` is locally CAT(0) by the link condition.
* `Y'` is the wedge of `Y_1^2` with a disk, so `Y' ≃ Y_1^2` and
  `pi_1(Y') = pi_1(Y_1^2)`.  In particular the finite residual `K` is the
  infinite simple subgroup of index 2 of
  `titz-witzel-simple-kazhdan-cat0-lattices-exist`; that citation is used
  only to describe `K`, not in the argument.
* `Lk_(Y')(y_0)` is disconnected, so by Part 1 `Y'` has no finite branched
  cover.  QED

## Why the monodromy step breaks

For `W`, `W°` (the vertices removed) has two components, one open square
each, and the small link sphere `S_c` is two arcs.  So the three inputs of
Step 4 of `sparse-branched-covers-sofic-pi1-reduction-proof` all fail: there
is no single path `gamma_c`, van Kampen does not apply to a disconnected
`W°`, and the trivial one-sheet covering of `W°`, completed by adding one
cone point to each component of the covering over the punctured cone, puts
two cone points over `c`, each with a one-edge link covering only half of
`Lk(c)`.  That is not a branched cover in the sense of the Setting.
