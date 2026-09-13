---
rg: 2
id: quasi-linear-groups-satisfy-permutational-boone-higman
kind: claim
title: Every finitely generated group of matrices over a finite product of fields, in any characteristics, lies in the permutational Boone--Higman class
distinct_from:
  global-field-soluble-linear-products-satisfy-boone-higman: that is soluble groups over products of number fields and positive-characteristic fields of transcendence degree at most one; this is every finitely generated group linear over any finite product of fields, with no solubility and no bound on transcendence degree.
  boone-higman-closed-under-finite-direct-products: that is closure of the plain Boone--Higman class under products, which is open; this stays inside B_A, where products are known to be harmless, so it needs no such closure.
  char-p-linear-groups-satisfy-permutational-boone-higman: that is one field of positive characteristic; this mixes factors of different characteristics, which no single field can carry.
  char-zero-linear-groups-satisfy-permutational-boone-higman: that is one field of characteristic zero; this is any finite product of fields.
artifacts:
  - research/artifacts/bh-quasi-linear-pbh-2026-09-13.md
---

**ESTABLISHED (2026-09-13)** through `quasi-linear-pbh-via-coordinate-projections`.
Independently reviewed: PASS (`research/artifacts/review-metabelian-bh-2026-09-13.md`, 2026-09-13).

**Statement.** Let `G` be a finitely generated group that embeds in
`GL_(n_1)(K_1) x ... x GL_(n_r)(K_r)`, where the `K_i` are fields of arbitrary
characteristics. Then `G` is in `B_A`, as defined in
`boone-higman-type-a-class-closed-under-finite-extensions`. So `G` has solvable
word problem and embeds in a finitely presented simple group.

Equivalently, in Wehrfritz's terms, `G` is a finitely generated quasi-linear
group: a group of matrices over a finite direct sum of fields. Indeed
`GL_n(K_1 ⊕ ... ⊕ K_r) = GL_n(K_1) x ... x GL_n(K_r)`, and block stabilization
makes the degrees equal.

**Examples.**
- `(Z wr Z) x (Z/p wr Z)`, which is linear over no single field (artifact
  `bh-metabelian-products-2026-09-12.md`, §2).
- `SL_3(F_2[s_1, s_2, s_3]) x SL_3(F_3[s_1, s_2, s_3]) x SL_3(Z[t])`.
- Every finitely generated metabelian group, by
  `fg-metabelian-groups-embed-in-products-of-coprimary-quotients`. This settles
  `fp-metabelian-groups-satisfy-boone-higman`.

**Credit.** Membership of each factor in `B_A` is
`char-zero-linear-groups-satisfy-permutational-boone-higman` and
`char-p-linear-groups-satisfy-permutational-boone-higman`. Closure of `B_A` under
products is Zaremsky's (arXiv:2405.18354, Proposition 5.6, as cited by BFFHZ; in arXiv:2405.18354 itself the product statement is Proposition 5.5). The
bounded novelty search is in the artifact.
