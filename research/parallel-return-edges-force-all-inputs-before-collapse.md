---
rg: 2
id: parallel-return-edges-force-all-inputs-before-collapse
kind: route
title: One forward edge stays on a cycle until all its parallel return edges are deleted
target: mf-closed-normal-joins-have-unbounded-minimal-arity
requires:
  - directed-seam-mf-closure-is-cycle-pruning
  - directed-seam-normal-lattice-is-vertex-edge-incidence
artifacts:
  - research/artifacts/pestov91-mf-closure-and-monotone-rules-2026-09-13.md
---

Section 3 uses two vertices, one forward edge and `m` parallel return
edges. Every proper subset of deleted return edges leaves every
retained edge on a cycle, hence gives a LEF quotient and closed input
product. Deleting all return edges leaves the one-edge just non-MF
group. The closure formula adds exactly its remaining simple edge
factor. The incidence count gives `2^(m+1)+3` normal subgroups in
the source and five in the full input quotient.
