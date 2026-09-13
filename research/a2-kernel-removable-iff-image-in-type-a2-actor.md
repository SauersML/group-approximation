---
rg: 2
id: a2-kernel-removable-iff-image-in-type-a2-actor
kind: claim
title: The kernel of a type [A_2] action can be removed by an embedding of pairs exactly when the action image embeds in a group admitting a type (A_2) action
distinct_from:
  a2-pairs-embed-in-a2-pairs-with-fng-kernels: that is the first part of FFWZ Question 5.9, removability for every type [A_2] pair; this shows that removability for one pair depends only on the image G/K, and is exactly membership of G/K in the permutational Boone--Higman class.
  a2-kernel-removal-forces-recursive-kernel: that is a computability obstruction to removal; this is an exact criterion for removal, and the obstruction follows from it because subgroups of type (A_2) actors have solvable word problem.
  relative-pbh-closed-under-finite-direct-products: that shows removability passes from two pairs to their product pair; this characterizes removability of a single pair by its image.
  permutational-boone-higman-conjecture: that asks every finitely generated group with solvable word problem to embed in a type (A_2) actor; this shows that removing the kernel of a type [A_2] pair is that conjecture's conclusion for the image group, which need not have solvable word problem.
---

**ESTABLISHED** by `a2-kernel-removal-via-product-with-image-actor` (elementary).

Terms are those of Fournier-Facio--Wu--Zaremsky, arXiv:2603.24687v2, read on
2026-09-13 from the PDF text on MSI
(`/scratch.global/sauer354/bh-reviewer/2603.24687.txt`).
- **Type [A_2] and type (A_2)** (Definition 1.3, lines 84–93). The action of `G`
  on a non-empty set `S` is of type [A_2] when `G` is of type `F_2`, `Stab_G(T)`
  is of type `F_(2−|T|)` for finite `T ⊆ S`, and the diagonal action on `S^2`
  has finitely many orbits. So `G` is finitely presented and point stabilizers
  are finitely generated. "If an action of type [A_n] … is moreover faithful, we
  say that it is of type (A_n)."
- **Embeds** (Definition 1.6, lines 151–153): "(G,N) embeds in (G′,N′) if there
  exists an injective homomorphism ι: G ֒→ G′ such that ι(G) ∩ N′ = ι(N)."
  Question 5.9 (lines 1339–1346) says "sharply embeds" for pairs, as Lemma 5.2
  does, and is read with this meaning.

**Statement.** Let `G` act on a non-empty set `S` with type [A_2] and kernel `K`.
The following are equivalent.
1. There are an action `G′ ↷ S′` of type [A_2], whose kernel `K′` is finitely
   normally generated in `G′`, and an injective `ι: G → G′` with
   `ι(G) ∩ K′ = ι(K)`.
2. `G/K` embeds in a group admitting an action of type (A_2).

Item 2 does not mention `S`: whether the kernel can be removed depends only on
the abstract group `G/K`.

**Consequences for the first part of FFWZ Question 5.9**
(`a2-pairs-embed-in-a2-pairs-with-fng-kernels`).
- **Reformulation.** The first part has a yes answer exactly when the action image
  of every type [A_2] action embeds in a group admitting a type (A_2) action. That
  is the conclusion of the permutational Boone--Higman conjecture (FFWZ Conjecture
  1.5), asked for all these image groups.
- **A no answer.** A non-removable pair has `G/K` outside that class. If `K` is
  recursive, `G/K` is finitely generated with solvable word problem, so a no answer
  with a recursive kernel would refute Conjecture 1.5.
- **Under PBH.** If Conjecture 1.5 holds, the first part is equivalent to the
  recursiveness of every type [A_2] kernel. Necessity is
  `a2-kernel-removal-forces-recursive-kernel` (b), which needs no assumption.
- **Positive cases.** The kernel is removable whenever `G/K` is known to embed in a
  type (A_2) actor. For example, when `G/K` is finitely presented, `G/K ↷ S` is
  itself of type (A_2), as in the proof of FFWZ Corollary 4.2.

**Not claimed.** No answer to Question 5.9 in either direction.
