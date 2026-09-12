---
rg: 2
id: oracular-local-block-holonomy-proof
kind: route
title: Gauge the common local packet along a spanning tree and isolate the chord product
target: oracular-local-block-detectors-miss-balanced-cycle-holonomy
requires:
  - finite-sheet-transport-networks-are-exactly-matricial
  - coherent-balanced-context-permutations-would-give-a-ce-trace
---

Use the common balanced packet and choose an intertwiner for every incidence.
Gauge intertwiners recursively along a spanning tree.  Schur decomposition
shows that the remaining freedom is a unitary on the equal-rank multiplicity
space.  Every non-tree edge records only the ordered product of these
unitaries around its fundamental cycle.  Altering that product changes no
vertex character or isotypic multiplicity.

`finite-sheet-transport-networks-are-exactly-matricial` realizes the same
statement already for arbitrary finite monodromy permutations, so no local
dimension inequality can remove the freedom.  Conversely,
`coherent-balanced-context-permutations-would-give-a-ce-trace` shows that
coherently killing all of these products for the non-CE source is precisely
the forbidden global step.  Hence the unresolved datum is cycle holonomy,
not local capacity.
