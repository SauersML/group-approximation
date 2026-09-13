---
rg: 2
id: faithful-finite-index-graphs-of-groups-have-type-a-overgroups
kind: claim
title: A faithful finite graph of finitely presented groups with finite-index edge inclusions embeds in a finitely presented group with a type (A) action
distinct_from:
  bliw-locally-finite-tree-actions-embed-in-fp-simple-groups: that imports the plain Boone--Higman conclusion of Bux--Llosa Isenrich--Wu Theorems B and 10.5; this is the permutational conclusion read off from the same proof, which puts these groups in the class closed under finite-index overgroups and finite products.
  free-generalized-bs-groups-have-type-a-overgroups: that imports the authors' Remark 12.7, the permutational conclusion for generalized Baumslag--Solitar groups over non-abelian free groups; this is the permutational conclusion for every faithful graph of groups covered by their Theorem 10.5 with n = 2.
  type-a-action-gives-boone-higman-for-subgroups: that turns a type (A) action into simple envelopes for subgroups of the actor; this supplies the actor.
---

**ESTABLISHED (read off from a literature proof).** Let `B_A` be as in
`boone-higman-type-a-class-closed-under-finite-extensions`.

1. Let `G` be the fundamental group of a finite graph of groups whose vertex
   groups are finitely presented and whose edge groups have finite index in the
   adjacent vertex groups. If `G` acts faithfully on its Bass--Serre tree, then
   `G` embeds in a finitely presented group `H` whose action on a countable set
   is of type (A) in the sense of `type-a-action-gives-boone-higman-for-subgroups`.
   So `G ∈ B_A`.
2. Let `G` act faithfully on a locally finite tree with finitely many orbits of
   vertices, and suppose the edge stabilizers are finitely presented. Then
   `G ∈ B_A`.

The actor `H` is the rigid permutation group of the augmented graph of groups of
Bux--Llosa Isenrich--Wu, arXiv:2408.05673v2, acting on the vertices of its
Bass--Serre tree.

**Credit.** All finiteness input is their Proposition 9.2 and Section 10. Their
Remark 12.7 states the permutational conclusion for `BS_(F_k)`. That the same
proof gives it under the hypotheses of their Theorem 10.5 is recorded here as a
reading of their proof. No priority is claimed, and I searched no further
literature.

**Consequences.** By items 1–3 of
`boone-higman-type-a-class-closed-under-finite-extensions`, every group
commensurable with a subgroup of a finite product of such groups embeds in a
finitely presented simple group, and its finitely generated subgroups have
solvable word problem.

**Trust surface.** The proofs of BLIW Proposition 9.2 and Lemmas 10.2–10.4 are
not re-checked. The Bass--Serre structure theorem, and finite presentation of
finite-index subgroups and overgroups of finitely presented groups, are used as
standard facts without re-reading.

Route: `faithful-graphs-type-a-via-bliw-rigid-permutation-groups`.
