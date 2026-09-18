---
rg: 2
id: pbh-wreath-closure-fails-over-undecidable-stabilizers
kind: claim
title: Some lamplighter Z/2 wr_(G/C) G with G = F_2 x F_2 and one lamp orbit has unsolvable word problem, so the permutational Boone--Higman class is not closed under permutational wreath products over arbitrary G-sets
distinct_from:
  pbh-closed-under-permutational-wreaths-with-infinite-stabilizers: that asserted closure over every countable G-set; this is the counterexample to that statement as written.
  bh-embeddability-forces-decidable-edge-membership: that is the same membership obstruction for HNN extensions and doubles; this is the lamp version, where the membership problem of a point stabilizer becomes a word problem.
  permutational-boone-higman-closed-under-wreath-products: that is the established case of finite point stabilizers, which always have decidable membership; nothing here touches it.
---

**ESTABLISHED** (lane proof, elementary, not reviewed; no priority claimed).

## Statement

Let `G` be a finitely generated group, `C <= G` a subgroup, `X = G/C` with the
left action, and `A != 1` a finitely generated group. Then:

1. `A wr_X G = A^(X) ⋊ G` is finitely generated, by `G` and one copy of `A`
   placed at the point `C`.
2. If `A wr_X G` has solvable word problem, then membership in `C` is decidable
   in `G`.

With Mihailova's subgroup (below), `Z/2 wr_(G/C) G` is not in `B_A` and embeds
in no finitely presented simple group. The groups `Z/2` and
`G = F_2 × F_2` are both in `B_A`. So the statement of
`pbh-closed-under-permutational-wreaths-with-infinite-stabilizers` is false.

## Proof

- **(1).** Write `δ_x^a` for the lamp with value `a` at `x`. Then
  `g δ_C^a g^(-1) = δ_(gC)^a`. `X` is a single orbit, so `G` and the lamps
  `δ_C^a` generate the base `A^(X)`, hence all of `A wr_X G`.
- **(2).** Fix `1 != a ∈ A`. For `g ∈ G`, the element
  `w_g = (g δ_C^a g^(-1)) (δ_C^a)^(-1) = δ_(gC)^a (δ_C^a)^(-1)` is `1` iff
  `gC = C`: lamps at distinct points of `X` lie in distinct direct factors of
  `A^(X)`. So `w_g = 1` iff `g ∈ C`. Given a word for `g`, a word for `w_g` is
  computed uniformly, so a solution of the word problem decides membership in `C`.
- **Counterexample.** By Mihailova's theorem, `F_2 × F_2` has a finitely
  generated subgroup `C` with undecidable membership problem (the fibre product of
  `F_2` onto a finitely presented group with unsolvable word problem). Take
  `G = F_2 × F_2`, `A = Z/2` and `X = G/C`. By (2), `Z/2 wr_X G` has unsolvable
  word problem.
- **Not in `B_A`.** Every finitely generated subgroup of a group with a type (A)
  action has solvable word problem (`type-a-action-gives-boone-higman-for-subgroups`).
  So the finitely generated group `Z/2 wr_X G` is not in `B_A`, and it embeds in
  no finitely presented simple group (`simple-envelope-forces-solvable-word-problem`).
- **Inputs are in `B_A`.** `F_2 <= V` and `V ∈ B_A`, being finitely presented,
  simple and MIF (BFFHZ Theorem C, `fp-simple-highly-transitive-groups-satisfy-pbh`).
  So `F_2 × F_2 <= V × V ∈ B_A` (`boone-higman-type-a-class-closed-under-finite-extensions`),
  and `Z/2 <= V`. `∎`

## Scope

- **Finite stabilizers.** Finite subgroups of a group with solvable word problem
  have decidable membership. That case is the theorem
  `permutational-boone-higman-closed-under-wreath-products`, and this does not
  touch it.
- **Corrected question.** The decidability hypothesis is necessary. The corrected
  form is `pbh-closed-under-decidable-permutational-wreaths`, which is OPEN.
- **Zaremsky's Question 5.7.** Zaremsky asks whether wreath products of groups
  with type (A) actions admit type (A) actions. Here `A`, `G` and `C` are all
  finitely generated, and the group has no type (A) overgroup at all. The
  obstruction sits in the *G-set*, through the membership problem of its
  stabilizer, not in the groups. So the question stays open for regular wreath
  products and for decidable G-sets.
