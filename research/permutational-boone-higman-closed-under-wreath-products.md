---
rg: 2
id: permutational-boone-higman-closed-under-wreath-products
kind: claim
title: If A and G satisfy permutational Boone--Higman, so does every restricted wreath product of A by G over a G-set with finite point stabilizers, in particular A wr G
distinct_from:
  boone-higman-type-a-class-closed-under-finite-extensions: that is closure of B_A under finite direct products and finite-index overgroups; this is closure under restricted wreath products with an infinite top group.
  aut-free-groups-satisfy-permutational-boone-higman: that imports BFFHZ Theorem A and Corollaries D and F, including closure under free products; this is closure under restricted wreath products.
  type-a-actors-closed-under-type-a-lamp-wreaths: that builds an actor on S x Y out of two given actors; this is the permanence property of the embedding class, which also needs free orbits at the top.
  bh-type-a-class-closed-under-permutational-lamp-wreaths: that allows finite lamp groups over a given actor and its own set; this allows any lamp group in B_A and any top group in B_A, over any set with finite stabilizers.
artifacts:
  - research/artifacts/solve-bh-free-solvable-2026-09-13.md
---

**ESTABLISHED** by `pbh-wreath-closure-via-free-relative-automorphism-orbits`. Not
independently reviewed.

## Statement

Let `A` and `G` be groups in `B_A`, the class of groups that embed in a group
admitting an action of type (A)
(`boone-higman-type-a-class-closed-under-finite-extensions`). Let `X` be a countable
`G`-set whose point stabilizers are finite. Then the restricted permutational wreath
product `A wr_X G = A^(X) ⋊ G` is in `B_A`. So it and all its subgroups embed in
finitely presented simple groups, and its finitely generated subgroups have
solvable word problem.

**Special cases.**
- The regular restricted wreath product `A wr G` (take `X = G`).
- Iterated wreath products such as `Z wr (Z wr (Z wr Z))`.
- `Z^r wr Aut(F_n)` (`aut-free-groups-satisfy-permutational-boone-higman`), and
  `Z wr H` for every finitely generated linear group `H` in characteristic zero
  (`char-zero-linear-groups-satisfy-permutational-boone-higman`).
- `V wr V`. `V` is in `B_A` by BFFHZ Theorem C, being finitely presented, simple and
  MIF; BFFHZ l.651--653 use it as "some finitely presented simple MIF group, for
  instance Thompson's group V".
- Every free solvable group (`free-solvable-groups-satisfy-permutational-boone-higman`).

## Relation to the literature

**Zaremsky's question.** Zaremsky, arXiv:2405.18354, Question 5.7 (TeX l.534--536). It
comes right after his Propositions 5.5 (products) and 5.6 (commensurability). The
number is read off the shared theorem counter of the TeX preamble. Read on MSI
2026-09-13:

> "If two groups $G$ and $H$ admit actions of type~(A) then does their free product
> $G*H$ admit an action of type~(A)? What about wreath products? Or general
> semidirect products?"

It is introduced by "Some related combination-type results are unclear to us even
for the permutational Boone--Higman conjecture, for example:".
- BFFHZ Corollary F settled free products in the embedding form of the permutational
  conjecture.
- This node settles restricted wreath products in the same embedding form, over sets
  with finite stabilizers.
- It does **not** show that `A wr G` itself admits an action of type (A).
- Infinite stabilizers stay open
  (`pbh-closed-under-permutational-wreaths-with-infinite-stabilizers`), as do general
  semidirect products.

**Nearby results.**
- Almeida, Dantas and Oliveira-Tosti (arXiv:2609.01868, TeX read on MSI) embed
  `Z^d wr_X G` in finitely presented simple groups for non-torsion contracting
  self-similar `G` satisfying their hypotheses, with `X = K\G`. They call this "the
  first result establishing the conjecture for this specific class of permutational
  wreath products". Their `K` can be infinite, so neither result contains the other.
- The bounded novelty search is in the artifact:
  - BFFHZ v2, whose only occurrence of "wreath" is `V wr_S Γ` in their definition of
    `SV_Γ`;
  - Fournier-Facio, Kropholler, Lyman and Zaremsky, arXiv:2506.02319, whose
    Boone--Higman section only treats Burger--Mozes actors;
  - Fournier-Facio, Wu and Zaremsky, arXiv:2603.24687;
  - two web searches.

  No printed proof was found, and no priority beyond that is claimed.

**Not covered.**
- Unrestricted wreath products, and hence arbitrary extensions through the
  Kaloujnine--Krasner embedding.
- Sets with infinite point stabilizers.
- General semidirect products `N ⋊ G`.
