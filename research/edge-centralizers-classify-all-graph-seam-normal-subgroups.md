---
rg: 2
id: edge-centralizers-classify-all-graph-seam-normal-subgroups
kind: route
title: Delete the edge factors contained in a normal subgroup, then centralization leaves only isolated vertex factors
target: directed-seam-normal-lattice-is-vertex-edge-incidence
requires:
  - directed-seam-mf-radical-is-exactly-the-acyclic-edge-kernel
  - three-torsion-kazhdan-seam-is-just-non-mf
  - binary-letter-repetition-realizes-matrix-amplification
  - unit-idempotent-elementary-group-has-three-torsion-generators
  - elementary-groups-over-fg-rings-have-property-t
artifacts:
  - research/artifacts/pestov91-directed-seams-and-normal-lattices-2026-09-13.md
---

Sections 3--4 supply the marking and lattice calculation. A fixed
binary delimiter gives clopen coding phases and a full matrix ring.
The endpoint factors are simple at this multiple-of-three rank by
letter repetition. For a normal subgroup, its intersection with the
edge kernel is a product `L_J`. After deleting those orbits, its image
centralizes every remaining finitary edge factor. The faithful edge
representation forces identity on each retained orbit and its endpoint
limits. The centralizer is precisely the product of isolated vertex
factors. Simplicity classifies its normal subgroups, yielding exactly
the pairs `(J,S)`. Their inclusion order proves the lattice and
connected-component assertions.
