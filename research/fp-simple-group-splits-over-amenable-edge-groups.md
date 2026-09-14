---
rg: 2
id: fp-simple-group-splits-over-amenable-edge-groups
kind: claim
title: Some finitely presented infinite simple group is a finite graph of hyperlinear groups over amenable edge groups
distinct_from:
  hyperlinear-fp-infinite-simple-group: That is the existence root; this is the specific structural input of its live route, and it is strictly more demanding.
  fg-simple-hyperlinear-tree-group-not-finitely-presented: That realizes this structure for finitely generated simple groups with locally finite stabilizers; this demands a finite presentation.
---

There is a finitely presented infinite simple group `S` that acts without
inversions on a tree, minimally and with finite quotient graph, whose vertex
stabilizers are hyperlinear and whose edge stabilizers are amenable.

If `S` is finitely presented and the edge groups are finitely generated, the
standard finiteness lemma for graphs of groups makes the vertex groups
finitely presented.  Because `S` is simple and not
virtually cyclic, the action is faithful and has no global fixed point.

## Attempts

- **Locally finite stabilizers** (Le Boudec's `G(F,F')^*`).  These give simple
  groups, but not finitely presented ones
  (`fg-simple-hyperlinear-tree-group-not-finitely-presented`).  Edge groups
  must be finitely generated.
- **Lattices in products of two trees** (Burger--Mozes type).  Dead for the
  splittings coming from either tree factor.  A cocompact lattice acting freely on the vertices of
  `T_1 x T_2` has `T_1`-vertex stabilizers acting properly and cocompactly on
  `T_2`, hence virtually free.  If they were amenable they would be
  virtually cyclic and `T_2` would be quasi-isometric to a line, which is
  impossible for a regular tree of degree at least three.
- **Finite edge groups.**  Expected dead: tree actions with finite stabilizer
  intersections tend to give acylindrically hyperbolic groups, which are not
  simple (Minasyan--Osin arXiv:1310.6289 with erratum arXiv:1711.09486).
  Recorded as a literature pointer only; no exact theorem statement was
  checked.
- **Live regime.**  Finitely generated infinite amenable edge groups such that
  every pairwise vertex-stabilizer intersection is infinite, while the
  fixator of the whole tree is trivial.  No example and no obstruction is
  recorded.  A first test case is torsion-free virtually polycyclic edge
  groups, where Hirsch length forces fixators along any geodesic extension of
  a minimal segment to be finite-index subgroups of one another.
