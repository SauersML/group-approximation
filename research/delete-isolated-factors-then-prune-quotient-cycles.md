---
rg: 2
id: delete-isolated-factors-then-prune-quotient-cycles
kind: route
title: Every normal quotient deletes edge orbits and isolated vertex components, so apply the exact graph radical to what remains
target: directed-seam-mf-closure-is-cycle-pruning
requires:
  - directed-seam-mf-radical-is-exactly-the-acyclic-edge-kernel
  - directed-seam-normal-lattice-is-vertex-edge-incidence
  - mf-relation-closure
artifacts:
  - research/artifacts/pestov91-mf-closure-and-monotone-rules-2026-09-13.md
---

Section 1 identifies the quotient by `N(J,S)` with the retained
graph after deleting `J` and the now-isolated vertices `S`, holding
rank fixed. Removing isolated vertices changes no cycles. The exact
radical theorem gives its noncycle edge kernels; pulling them back
gives `N(J union B_J,S)`. The cycle-core quotient is LEF and preserves
every edge factor having a return path, proving the visibility clause.
