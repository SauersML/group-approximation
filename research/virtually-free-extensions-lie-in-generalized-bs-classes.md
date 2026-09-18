---
rg: 2
id: virtually-free-extensions-lie-in-generalized-bs-classes
kind: claim
title: Every extension of a finitely generated infinite group N by a finitely generated virtually free group lies in the generalized Baumslag–Solitar class BS_N
distinct_from:
  bliw-locally-finite-tree-actions-embed-in-fp-simple-groups: that imports the tree theorems of Bux–Llosa Isenrich–Wu; this is the elementary membership lemma that feeds extensions into their class BS_N.
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that imports the free-by-cyclic case; this puts every N-by-(virtually free) extension, split or not, into BS_N.
artifacts:
  - research/artifacts/gq-bh-bh-free-extensions-bliw-section-11-12.md
---

**ESTABLISHED** (lane proof, elementary, not reviewed; route
`virtually-free-extensions-lie-in-generalized-bs-classes-proof`).

Let `1 -> N -> G -> Q -> 1` be exact, with `N` finitely generated and infinite and `Q` finitely
generated and virtually free (finite groups allowed). Then `G` is the fundamental group of a finite
graph of groups whose vertex and edge groups all contain `N` with finite index, and whose edge
inclusions have finite index. So `G ∈ BS_N` in the sense of Bux–Llosa Isenrich–Wu §11
(recorded in the artifact).

In particular every `N`-by-free group `N ⋊ F_m` and every `N`-by-cyclic group lies in `BS_N`.
