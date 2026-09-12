---
rg: 2
id: global-field-soluble-linear-products-satisfy-boone-higman
kind: claim
title: Finitely generated soluble groups linear over finite products of number fields and positive-characteristic fields of transcendence degree at most one satisfy permutational Boone--Higman
distinct_from:
  positive-char-surface-linear-groups-satisfy-boone-higman: that settles one positive characteristic at a time, through Leavitt tensor envelopes whose permanence under products is unknown; this settles soluble products across different characteristics and with number fields, inside the permutational class B_A, at transcendence degree at most one.
  algebraic-linear-groups-satisfy-boone-higman: that is Boone--Higman for linear groups over one number field; this puts those groups in B_A and combines them with positive-characteristic soluble factors.
  boone-higman-type-a-class-closed-under-finite-extensions: that is the permanence of B_A under products and finite extensions; this is a new family of inputs for that permanence, built from self-similar envelopes.
artifacts:
  - research/artifacts/bh-metabelian-products-2026-09-12.md
---

**ESTABLISHED.** Let `G` be a finitely generated soluble group, and suppose `G`
embeds in `GL_(n_1)(K_1) x ... x GL_(n_k)(K_k)`, where each field `K_i` is
- algebraic over `Q`, or
- of positive characteristic with transcendence degree at most one over its
  prime field.

Then `G` lies in `B_A`: it embeds in a group admitting an action of type (A). So
`G` has solvable word problem and embeds in a finitely presented simple group.

**Instances of Problem 5.3(7)** (finitely presented metabelian groups, BBMZ
arXiv:2306.16356v3):
- **Baumslag's metabelian groups over F_p.** `B_p = F_p[x^±1, (1+x)^-1] x| Z^2`
  satisfies Boone--Higman in the permutational form. Its envelope passes through
  Bux's theorem and Zaremsky's Theorem 1.1, with no Leavitt input.
- **Mixed characteristics.** Products such as `B_2 x B_3 x BS(1,6)`, and all
  their finitely generated subgroups, are finitely generated metabelian groups
  that are linear over no single field. No earlier envelope covered them: the
  Leavitt tensor envelopes live in one characteristic, and closure of
  Boone--Higman under products is open
  (`boone-higman-closed-under-finite-direct-products`).
- **All mixed products at this dimension.** More generally, every finitely
  generated metabelian group that embeds in a product of linear groups over
  number fields and positive-characteristic fields of transcendence degree at
  most one.

**Credit and novelty.**
- **Every ingredient is published.**
  - Zaremsky's Theorem 1.1 and Example 4.7, and Bux's Borel theorem.
  - Kochloukova--Sidki's Theorem A, arXiv:1710.04745. It already gives the
    finitely presented self-similar upper triangular hosts over `F_p(x)` that
    contain Baumslag's `B_p`.
  - BFFHZ Remark 3.5 and Theorem C, and permanence of `B_A` (Zaremsky's
    Propositions 5.5 and 5.6, as cited by BFFHZ).
- **The combination is routine.** The mixed-characteristic class stated here was
  not found written down in the bounded source set:
  - the survey arXiv:2306.16356v3;
  - BFFHZ arXiv:2503.21882v2 and FFWZ arXiv:2603.24687v2;
  - Zaremsky arXiv:2405.09722;
  - Kochloukova--Sidki arXiv:1710.04745 and arXiv:2509.05798;
  - this repository's Boone--Higman frontier artifact.

  No priority is claimed beyond recording it.

**Boundary.**
- **Characteristic zero:** transcendence degree zero is the limit of the affine
  self-similar route (`affine-self-similar-coordinate-rings-are-one-dimensional`).
- **Positive characteristic:** degree one is the limit of the finite-index
  principal ideal criterion. What remains of Problem 5.3(7) is recorded in
  `fp-metabelian-groups-satisfy-boone-higman`.

The derivation is `global-field-soluble-linear-products-proof`.
