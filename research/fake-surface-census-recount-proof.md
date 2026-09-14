---
rg: 2
id: fake-surface-census-recount-proof
kind: route
title: Recount acyclic cellular fake surfaces from per-edge sheet matchings and match the published list against the recount
target: fake-surface-census-misses-acyclic-classes
requires: []
artifacts:
  - research/artifacts/hl-andrews-curtis-fake-surfaces-2026-09-14.md
---

**Model.** Let F be a cellular fake surface of complexity t ≥ 1.
- **Singular set.** Its triple lines and vertices form a connected 4-regular
  multigraph Γ, with t vertices and 2t edges; a loop counts twice.
- **Vertices.** A vertex has a neighbourhood that is the cone on the 1-skeleton of
  a tetrahedron. So the six sheet corners at v are the six pairs of half-edges at v.
- **Edges.** An edge has a neighbourhood T × I. Its three sheets are matched between
  the two ends by a bijection, one of six.
- **Disks.** The regular neighbourhood N(Γ) is determined by Γ and these 2t
  bijections. Following a sheet corner along an edge to the matched corner at the
  other end traces the boundary circles of N(Γ). For a cellular F, a disk is glued
  to each circle.

Conversely, every choice of bijections gives a cellular fake surface. A PL
homeomorphism preserves the intrinsic stratification. So homeomorphism classes on Γ
are the orbits of the half-edge automorphism group of Γ: bijections of half-edges
preserving the vertex partition and the edge pairing.
- **Acyclicity.** χ = 1 forces t+1 disks. H₁ = 0 exactly when the exponent-sum
  matrix of the disks, on the non-tree edges of a spanning tree, has determinant ±1.
- **Why the spanning tree suffices.** The top homology of a 2-complex is free and
  its rank is then 0.

**Recount.** `experiments/andrews-curtis-fake-surfaces/fsenum.cpp` (MSI job 779877):
- It generates the connected 4-regular multigraphs up to isomorphism, as maximal
  adjacency matrices. For t = 1, …, 6 it gives 1, 2, 4, 10, 28 and 97 graphs, as in
  Table `tab:complexity_table` of arXiv:2406.09439v3.
- It runs over all 6^{2t} bijection choices on each graph and keeps the acyclic
  ones.
- It keeps the orbit minima under the half-edge automorphism group: all
  adjacency-preserving vertex permutations, then all edge images and orientations.
- **Orbit–stabilizer check, on every graph.** The sum of |Aut|/|Stab| over the kept
  classes equals the number of acyclic choices.
- **Automorphism counts.** An independent brute force, `autcheck.py`, over vertex
  permutations and per-vertex half-edge bijections gives the same |Aut| on every
  graph with t ≤ 4.
- **Second implementation.** `fsac.py`, written independently in Python, recomputes
  disks, disk lengths and determinants for all 116,394 classes with t ≤ 5, with 0
  disagreements.
- **Totals.**
  - t = 1, 2, 3, 4: 2, 17, 239, 4676 classes.
  - t = 5: 111,460 classes, 517 of them without small disks.

**Match.** `diag2.py` reads each row of `fakesurfaces.csv` and tries both
orientations of every non-loop edge. It rebuilds the per-edge bijections, checks
that the 6t corners are each used exactly once, and canonicalizes under the same
automorphism group.
- All 238, 4618 and 514 rows land in distinct classes, and none is unmappable.
- The classes left over number 1, 58 and 3.

**Cause, explicitly.** Complexity 3, graph 3 (a loop, two single edges, a triple
edge). Codes 435 and 477 have disk words
`[1,2,5,-3,-1,2,4,-5,4,-3,1], [2,6,-3], [4,-6], [5,-6]` and
`[1,2,6,-3,-1,2,4,-5,4,-3,1], [2,5,-3], [4,-6], [5,-6]`.
- `are_same` from the census code returns True through 16 letter maps. Each has
  5 ↦ 6 but −5 ↦ −5, and 4 ↦ 4 but −4 ↦ −6, so none is a relabeling of edges.
- `samecheck2.py` tries all 24 edge-preserving half-edge bijections of this graph.
  None carries 435 to 477.

**Trust surface.** The combinatorial model above (standard for generic
2-polyhedra), the two implementations, and the cited file revision.
