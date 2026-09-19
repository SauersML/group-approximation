---
rg: 2
id: pbh-coset-wreaths-iff-identity-edge-hnns
kind: claim
title: For G in the permutational Boone--Higman class and any subgroup C, the lamplighter over G/C, the identity-edge HNN extension over C, and realizing C as a centralizer in an overgroup are equivalent
distinct_from:
  free-permutational-products-preserve-pbh: that proves one implication, lamplighter over X ⟹ free permutational product over X, and uses it for finite stabilizers; this closes the circle into an equivalence and adds the centralizer criterion.
  pbh-closed-under-decidable-permutational-wreaths: that is the open closure for decidable stabilizers; this shows it is equivalent to the identity-edge HNN closure for the same subgroups, and to a centralizer realization problem.
  bh-embeddability-survives-decidable-edge-hnn: that is the open HNN permanence for embeddability into fp simple groups; its identity-edge case in the permutational class is condition (d) here.
  pbh-class-closed-under-graph-products: that realizes X *_C (C x K) for retracts C; retracts are one of the centralizer cases (e) listed here.
---

**ESTABLISHED** by `pbh-coset-wreaths-iff-identity-edge-hnns-proof` (lane proof, not
reviewed; no priority claimed). `B_A` is the class of groups that embed in a group
admitting an action of type (A).

## Statement

Let `G ∈ B_A` and let `C <= G` be any subgroup. The following are equivalent.

- **(a)** `Z/2 wr_(G/C) G ∈ B_A`.
- **(b)** `A wr_(G/C) G ∈ B_A` for every `A ∈ B_A`.
- **(c)** `G *_C (C × K) ∈ B_A` for every `K ∈ B_A`. This group is the free permutational
  product `(*_(G/C) K) ⋊ G`.
- **(d)** The identity-edge HNN extension `G *_C (C × Z) = <G, t | t c t^(-1) = c (c ∈ C)>`
  lies in `B_A`.
- **(e)** There are a group `L ∈ B_A` containing `G` and an element `m ∈ L` with
  `C_G(m) = C`.

**Multiple orbits.** Let `X` be a countable `G`-set with stabilizers `C_i`. If one
group `L ∈ B_A` realizes every `C_i` as in (e), then `A wr_X G` and `(*_X K) ⋊ G` lie in
`B_A` for all `A, K ∈ B_A`. For finitely many orbits it is enough that each `C_i`
satisfies (e) on its own.

## When (e) holds

Condition (e) holds in each of the following cases.
1. **`C` finite.** Take `L = Z/2 wr_(G/C) G` (`permutational-boone-higman-closed-under-wreath-products`)
   and `m` the lamp at the coset `C`.
2. **`C` a centralizer.** `C = C_G(S)` for a finite set `S ⊂ G`.
3. **`C` a retract** of `G` with retraction `r`. Take `L = G wr Z/2`, embed `G` by
   `g -> (g, r(g))`, and take `m` the swap.
4. **`C` a fixed subgroup.** `C = Fix(α)` for an automorphism `α` of `G` with
   `G ⋊_α Z ∈ B_A`. Take `m` the stable letter.
5. **Finite intersections** of subgroups satisfying (e). Embed `G` diagonally in
   `L_1 × L_2`.

Every subgroup satisfying (e) has decidable membership in `G` when `G` is finitely
generated: `g ∈ C` iff `[g, m] = 1` in `L`, and `L` has solvable word problem on
finitely generated subgroups. The Mihailova subgroups of
`pbh-wreath-closure-fails-over-undecidable-stabilizers` fail (a)–(e).

## Consequence

The following three statements are equivalent, for finitely generated `G ∈ B_A` and
subgroups `C` with decidable membership:
- the open wreath closure `pbh-closed-under-decidable-permutational-wreaths`;
- the permutational form of the identity-edge case of
  `bh-embeddability-survives-decidable-edge-hnn`, that is (P2) of its Attempt 9;
- **centralizer realization:** every such `C` is `C_G(m)` for some `m` in some
  `B_A`-overgroup of `G`.

The first two are OPEN, so the third is too.
