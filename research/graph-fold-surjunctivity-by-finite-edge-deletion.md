---
rg: 2
id: graph-fold-surjunctivity-by-finite-edge-deletion
kind: route
title: Enlarge the vertex groups faithfully and delete finite edge sets in the free kernel graph
target: graph-folds-over-surjunctive-groups-are-surjunctive
requires: []
artifacts:
  - research/artifacts/surjunctivity-graph-folds-2026-09-11.md
  - research/artifacts/finitary-split-extension-surjunctivity-2026-09-11.md
  - research/artifacts/rf-lamp-wreath-surjunctivity-2026-09-11.md
---

The linked proof gives the complete argument. Sections 4--5 embed the
input graph of groups in a split extension `N semidirect G` whose kernel
is `pi_1(Y,o)` for a graph action fixing every vertex. The embedding is
injective because a vertex element enters an enlarged edge image exactly
when it was already in the original edge group.

Section 3 verifies the finitary hypotheses using the free basis attached
to a chosen spanning tree. For a loop `ell=e_1^eps_1 ... e_r^eps_r`, the
exact action formula is `g.[ell]=product b_(g e_j)^eps_j`, with tree-edge
symbols equal to one. This proves finite support and stabilizer invariance
even when the action moves the chosen tree.

Section 2 records the preexisting marked-site peeling theorem and audits
the compatibility of extensions across the finite quotient subgroups.
The cited complete proofs transplant an injective automaton to separating
coset spaces, peel proper finite subsets, and apply surjunctivity of
pointwise stabilizer subgroups to the final exceptional cosets. They
therefore establish surjunctivity of the host, and subgroup heredity
finishes the proof for the original fundamental group.

The finite-memory peeling theorem is inherited from the earlier shared
artifacts; the new proof contribution is the vertex-fixed graph kernel
and its application to arbitrary compatible graph-of-groups diagrams.
