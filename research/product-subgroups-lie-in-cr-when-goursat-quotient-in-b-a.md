---
rg: 2
id: product-subgroups-lie-in-cr-when-goursat-quotient-in-b-a
kind: claim
title: A subgroup H of G_1 x G_2 with finitely generated projections, where G_1 and G_2 are LR groups in B_A (free, limit, surface groups), satisfies the coset-wreath conditions whenever its Goursat quotient lies in B_A; for products of free groups H in CR forces the quotient to have solvable word problem
distinct_from:
  fibre-products-over-b-a-quotients-lie-in-cr: that treats the symmetric fibre product of one map F -> Q inside F x F; this treats every subgroup with finitely generated projections of a product of two LR groups, through Goursat's lemma and virtual retractions.
  pbh-coset-wreath-subgroups-closure-properties: that gives the closure operations; this combines them to control all such subgroups of products by one quotient group.
  pbh-closed-under-decidable-permutational-wreaths: that is the open closure over all G in B_A; this reduces its instances over products of free groups with finitely generated stabilizers to membership of their Goursat quotients in B_A.
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

**ESTABLISHED** by `product-subgroups-lie-in-cr-when-goursat-quotient-proof` (lane proof;
not independently reviewed; no priority claimed). `CR(G)` is as in
`pbh-coset-wreath-subgroups-closure-properties`.

## Statement

Let `G_1, G_2 ∈ B_A` be groups in which every finitely generated subgroup is a virtual retract
(property (LR)). Examples: free groups of finite rank, limit groups, closed surface groups;
see `virtual-retracts-satisfy-pbh-coset-wreath-closure`. Let `H ≤ G_1 × G_2`, with projections
`F_i = p_i(H)` finitely generated, and put `L_1 = H ∩ (G_1 × 1)`.
- **Goursat quotient.** By Goursat's lemma, `Q_H = F_1/L_1` is isomorphic to `F_2/L_2`, and
  `H = {(a, b) ∈ F_1 × F_2 : φ_1(a) = φ_2(b)}` for the two induced maps `φ_i : F_i → Q_H`.

1. **Positive.** If `Q_H ∈ B_A`, then `H ∈ CR(G_1 × G_2)`. So all of the following lie in `B_A`
   for all `A, K ∈ B_A`:
   - `A ≀_{(G_1×G_2)/H} (G_1 × G_2)`;
   - `(G_1 × G_2) *_H (H × K)`;
   - the double `(G_1 × G_2) *_H (G_1 × G_2)`.
2. **Necessity of a solvable word problem.** If `G_1, G_2` are finitely generated with solvable
   word problem and `H ∈ CR(G_1 × G_2)`, then `Q_H` has solvable word problem.
3. **Products of free groups.** For every finitely generated `H ≤ F_m × F_n`,
   `Q_H ∈ B_A ⟹ H ∈ CR(F_m × F_n) ⟹ Q_H has solvable word problem`.
   Under the permutational Boone–Higman conjecture the three conditions are equivalent. Every
   finitely presented group arises as `Q_H` for a finitely generated `H` (Mihailova).

## Lesson for general BH

Over products of free groups, the decidable-wreath (identity-edge HNN) closure of `B_A` asks
nothing beyond permutational Boone–Higman for the Goursat quotients.
- Every finitely generated stabilizer `H` is controlled by one quotient `Q_H`.
- `Q_H ∈ B_A` gives the closure for `H`, and an unsolvable word problem of `Q_H` refutes it.
- So these combination problems cannot be easier than PBH for finitely presented groups, and
  a counterexample there would be a counterexample to PBH.

The mechanism is general:
- intersections, preimages and retracts make `CR` behave like a Boolean algebra of "definable"
  subgroups;
- virtual retracts move everything to a finite-index subgroup;
- the monomial embedding brings it back.

What remains hard is the *twisted* edge maps, which `CR` does not see.
