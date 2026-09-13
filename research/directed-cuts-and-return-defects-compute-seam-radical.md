---
rg: 2
id: directed-cuts-and-return-defects-compute-seam-radical
kind: route
title: Directed cuts give one defect on every crossing edge, while cycle walks give LEF models for the remaining graph
target: directed-seam-mf-radical-is-exactly-the-acyclic-edge-kernel
requires:
  - subshift-ring-lef-iff-word-edges-lie-on-cycles
  - short-period-free-subshift-mf-dichotomy-reaches-unit-groups
  - finite-additive-order-one-sided-defects-are-mf-invisible
  - heteroclinic-subshift-has-prescribed-mf-quotient
artifacts:
  - research/artifacts/pestov91-directed-seams-and-normal-lattices-2026-09-13.md
  - research/torsion-defect-one-auxiliary-coordinate-proof.md
---

Sections 1--2 prove the deletion kernel and both radical inclusions.
Every symbolic bridge on a cycle closes in each finite word graph,
so deleting the noncycle edges leaves a LEF ring. For each bad edge,
the vertices reachable from its target define a forward-closed cut.
In a bounded-gap return section the cut indicator has one defect
point on every crossing edge. The printed rank-four obstruction and
tower embedding give an invisible element with nontrivial component
on the chosen finitary factor. A commutator isolates that factor;
its simplicity kills it all. The LEF retained image gives equality.
