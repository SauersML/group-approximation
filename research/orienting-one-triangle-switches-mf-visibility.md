---
rg: 2
id: orienting-one-triangle-switches-mf-visibility
kind: route
title: Orient the same triangle cyclically or transitively and apply the cycle radical and incidence lattice formulas
target: matched-triangle-kazhdan-extensions-have-opposite-mf-status
requires:
  - directed-seam-mf-radical-is-exactly-the-acyclic-edge-kernel
  - directed-seam-normal-lattice-is-vertex-edge-incidence
artifacts:
  - research/artifacts/pestov91-directed-seams-and-normal-lattices-2026-09-13.md
---

Section 5 compares `0->1->2->0` with the transitive orientation
`0->1`, `1->2`, `0->2`, using the same endpoint system at all vertices.
Both alphabets have nine symbols, giving coding length 12 and rank
36. The incidence data is unchanged; the normal-subgroup counts for
deleting zero, one, two or three edges are `1,3,6,8`, totaling 18.
All cycle edges survive in the first graph, and all edges are killed
in the second. The other group properties follow from the common
marking and normal-lattice theorem.
