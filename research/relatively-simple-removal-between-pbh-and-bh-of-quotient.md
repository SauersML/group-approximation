---
rg: 2
id: relatively-simple-removal-between-pbh-and-bh-of-quotient
kind: claim
title: A finitely presented relatively simple pair can remove its largest normal subgroup if its simple quotient embeds in a type (A_2) actor, and only if that quotient embeds in a finitely presented simple group
distinct_from:
  fp-relatively-simple-pairs-embed-with-fng-kernels: that is the second part of FFWZ Question 5.9, removability for every finitely presented relatively simple pair; this proves, for one pair, that removability follows from the permutational Boone--Higman property of its simple quotient and implies the classical one.
  a2-kernel-removable-iff-image-in-type-a2-actor: that is an exact criterion for type [A_2] pairs, the setting of the first part of Question 5.9; this is the second part, where the product actor has to be turned into a relatively simple group and only a sufficient and a necessary condition are proved.
  abstract-btb-pairs-fp-and-relatively-simple: that imports FFWZ Theorem 3.6, Theorem 4.1(ii) and Lemma 5.2 for an arbitrary type [A_2] action; this applies them to the product actor G x Λ built from the pair and an actor for its simple quotient.
  a2-kernel-removal-forces-recursive-kernel: that is the computability obstruction for type [A_2] pairs; this includes the analogous obstruction for relatively simple pairs, in item (b).
---

**ESTABLISHED** by `relatively-simple-removal-via-twisted-product-actor`.

Terms are those of Fournier-Facio--Wu--Zaremsky, arXiv:2603.24687v2, read on
2026-09-13 from the PDF text on MSI
(`/scratch.global/sauer354/bh-reviewer/2603.24687.txt`): normal pairs and
relative simplicity (Definitions 1.1 and 1.2, lines 53–59), embeddings of pairs
(Definition 1.6, lines 151–153), and types [A_2] and (A_2) (Definition 1.3,
lines 84–93), as recorded in `a2-kernel-removable-iff-image-in-type-a2-actor`.

**Statement.** Let `(G,N)` be a finitely presented relatively simple pair.
- **(a)** Suppose `G/N` embeds in a group admitting an action of type (A_2). Then
  there are a finitely presented relatively simple pair `(G′,N′)`, with `N′`
  finitely normally generated in `G′`, and an injective `ι: G → G′` with
  `ι(G) ∩ N′ = ι(N)`. One may take `G′ = SV_H` and `N′ = SK_H` for an explicit
  type [A_2] actor `H = G x Λ`.
- **(b)** Conversely, if such `(G′,N′)` and `ι` exist, then `G/N` embeds in the
  finitely presented simple group `G′/N′`. In particular `G/N` has solvable word
  problem, and `N` is recursive.

**Consequences for the second part of FFWZ Question 5.9**
(`fp-relatively-simple-pairs-embed-with-fng-kernels`).
- **A no answer.** A non-removable pair has a simple quotient `G/N` outside the
  permutational Boone--Higman class. If `N` is recursive, `G/N` is finitely
  generated with solvable word problem, so a no answer with recursive `N` would
  refute FFWZ Conjecture 1.5 (PBH).
- **Under PBH.** If Conjecture 1.5 holds, the second part is equivalent to
  recursiveness of the largest normal subgroup of every finitely presented
  relatively simple group.
- **A link with the first part.** Suppose the first part of Question 5.9 holds,
  and `G/N` embeds in the image `A/K` of some type [A_2] action. By
  `a2-kernel-removable-iff-image-in-type-a2-actor`, `A/K`, hence `G/N`, embeds in a
  type (A_2) actor. By (a), `(G,N)` is then removable. So the first part gives the
  second for every pair whose simple quotient lies inside a type [A_2] action
  image. For other pairs the link stays open.

**Not claimed.** No answer to Question 5.9 in either direction, and no
equivalence in (a)–(b): closing the gap between them is the question whether the
Boone--Higman and permutational Boone--Higman properties agree for `G/N`.
