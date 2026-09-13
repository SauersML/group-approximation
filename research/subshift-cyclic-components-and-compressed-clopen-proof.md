---
rg: 2
id: subshift-cyclic-components-and-compressed-clopen-proof
kind: route
title: Model cyclic components separately and turn a transient edge into a one-sided inverse
target: subshift-ring-lef-iff-word-edges-lie-on-cycles
requires: []
artifacts:
  - research/artifacts/pestov91-subshift-lef-mf-dichotomy-2026-09-13.md
---

Sections 1--3 give the full proof. An edge outside a directed cycle
determines a forward-closed reachable set excluding its source. Its
clopen cylinder union is strictly compressed by the shift. The displayed
inverse pair then violates direct finiteness.

When every edge lies on a cycle, the word graph is a disjoint union of
strongly connected components. Choose an edge-covering closed walk in
each component and enlarge each matrix period beyond the relevant
crossed-product degree bound. Their union realizes exactly the required
finite language. Distinct degrees occupy disjoint matrix diagonals, so
the finite product of matrix rings detects precisely the zero expressions
in any prescribed finite ring table. This proves unital ring-LEF, which
implies stable finiteness and hence direct finiteness. The inverse-pair
calculation also shows that direct finiteness excludes every compressed
clopen set, closing the equivalences.
