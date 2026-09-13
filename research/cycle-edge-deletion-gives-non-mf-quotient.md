---
rg: 2
id: cycle-edge-deletion-gives-non-mf-quotient
kind: route
title: Delete one edge of a two-cycle so that its LEF seam group maps onto a just non-MF one-edge group
target: lef-kazhdan-group-has-non-mf-quotient-by-simple-locally-finite
requires:
  - directed-seam-mf-radical-is-exactly-the-acyclic-edge-kernel
  - directed-seam-normal-lattice-is-vertex-edge-incidence
artifacts:
  - research/artifacts/pestov91-directed-seams-and-normal-lattices-2026-09-13.md
---

Section 6 uses the two opposite directed edges between two vertices.
Both lie on a cycle, so the source is LEF. Deleting one isolated orbit
has its infinite simple finitary group as exact kernel. The remaining
edge lies on no cycle, so its kernel is exactly the nontrivial MF
radical of the quotient. The incidence formula gives seven normal
subgroups in the source and five in the quotient, whose proper
quotients are the simple endpoint factors, their product and `1`.
Keep the original rank thirty and restrict its binary marking to
preserve the three torsion-generator formulas.
