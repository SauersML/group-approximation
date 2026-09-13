---
rg: 2
id: product-of-two-trees-lattices-satisfy-permutational-boone-higman
kind: claim
title: Every cocompact lattice in the automorphism group of a product of two locally finite trees satisfies permutational Boone--Higman
distinct_from:
  free-generalized-bs-groups-have-type-a-overgroups: that imports Bux--Llosa Isenrich--Wu Remark 12.7 for the class BS_(F_k); this shows that every cocompact lattice in a product of two trees, one of them with more than two ends, belongs to BS_(F_2), including the non-residually-finite lattices.
  bliw-locally-finite-tree-actions-embed-in-fp-simple-groups: that needs a faithful cocompact action on one tree with finitely presented edge stabilizers and gives a plain embedding; this needs no faithfulness on either factor and gives the permutational form.
  radu-bmw-lattice-splits-as-amalgams-of-virtually-free-groups: that computes the two Bass--Serre splittings of one explicit lattice; this is the general membership in BS_(F_2), of which Radu's lattice is one instance.
---

**ESTABLISHED** through `product-of-two-trees-lattices-pbh-proof`. Not
independently reviewed.

Let `T_1`, `T_2` be locally finite trees, at least one of which has more than
two ends. Let `Gamma` act on the square complex `T_1 x T_2` by automorphisms
that preserve the product decomposition, where an element may swap the two
factors. Suppose that every vertex stabilizer is finite and that there are
finitely many `Gamma`-orbits of vertices. Then:

1. the subgroup `Gamma_0` of elements preserving each factor has index at most
   2, and `Gamma_0` lies in `BS_(F_2)`;
2. `Gamma` embeds in a finitely presented group admitting an action of type (A),
   so `Gamma` lies in the class `B_A` of
   `boone-higman-type-a-class-closed-under-finite-extensions`;
3. every subgroup of `Gamma` embeds in a finitely presented simple group, and
   every finitely generated subgroup has solvable word problem.

The hypotheses hold for every discrete cocompact subgroup of
`Aut(T_1) x Aut(T_2)` when `T_2` has more than two ends.

## Members

- **Radu's lattice.** `Gamma_R` of `radu-bmw-lattice-embeds-in-titz-witzel-kernel`
  acts simply transitively on the vertices of a product of two 3-regular trees.
  It is not residually finite, so no linear or self-similar host can contain it.
- **Wise and Burger--Mozes.** Titz Mite--Witzel (arXiv:2509.05054v2,
  `non-rf.tex` l.248) describe "the irreducible lattices of products of trees
  first studied by Wise, Burger and Mozes" as "the first known non-residually
  finite lattices on two-dimensional buildings". For the Burger--Mozes groups
  the permutational form is already their Remark 12.7.
- **Reducible lattices** such as `F_m x F_n`.

## Scope and credit

- **Credit.** The membership argument is elementary Bass--Serre theory. BLIW
  state membership in `BS_(F_2)` for the Burger--Mozes groups and the
  free-by-cyclic groups, and don't state the general lattice case. No priority
  is claimed. The literature search was BLIW, the BBMZ survey and one web
  search.
- **Trust surface** (standard, not re-read here): the Bass--Serre structure
  theorem, and the theorem that the fundamental group of a finite graph of
  finite groups is finitely generated and virtually free.
- **Not covered:**
  - lattices in products of three or more trees;
  - lattices in irreducible Euclidean buildings;
  - general CAT(0) groups (`cat0-groups-satisfy-boone-higman`).
