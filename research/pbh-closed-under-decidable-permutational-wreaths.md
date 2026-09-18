---
rg: 2
id: pbh-closed-under-decidable-permutational-wreaths
kind: claim
title: The permutational Boone--Higman class is closed under permutational wreath products over G-sets with finitely many orbits whose point stabilizers have decidable membership
distinct_from:
  pbh-closed-under-permutational-wreaths-with-infinite-stabilizers: that asked for every countable G-set and is refuted by pbh-wreath-closure-fails-over-undecidable-stabilizers; this adds the decidability hypothesis that the refutation shows is necessary.
  permutational-boone-higman-closed-under-wreath-products: that is the established case of finite point stabilizers; this allows infinite stabilizers with decidable membership.
  free-permutational-products-preserve-pbh: that is the free-product analog, established for finite stabilizers; by that node, this claim implies the free-product analog for the same G-sets.
---

**OPEN.** Let `A, G ∈ B_A` with `G` finitely generated, and let `X` be a `G`-set
with finitely many orbits `G/C_1, ..., G/C_n`. Suppose each `C_i` has decidable
membership in `G`. Then `A wr_X G = A^(X) ⋊ G` lies in `B_A`.

## Why this form

- **The hypothesis is necessary** for finitely generated `A != 1`:
  `pbh-wreath-closure-fails-over-undecidable-stabilizers` shows that the word problem
  of `A wr_(G/C) G` decides membership in `C`.
- **It is also what the word problem needs.** If `A` and `G` have solvable word
  problems and each `C_i` has decidable membership, then `A wr_X G` has solvable word
  problem: an element `(f, g)` is trivial iff `g = 1` and every lamp value is `1`.
  The support of `f` is a finite list of cosets, and equality of cosets `g C_i = g' C_i`
  is decided by membership of `g^(-1) g'` in `C_i`. So no decidability obstruction
  remains, and the claim is a special case of `boone-higman-conjecture` in its
  permutational form.
- **Finite stabilizers** are the established case
  `permutational-boone-higman-closed-under-wreath-products`.

## Consequence

By `free-permutational-products-preserve-pbh`, this claim for `A = Z/2` implies that
`(*_X K) ⋊ G` lies in `B_A` for every `K ∈ B_A` over the same `G`-sets. In particular
the centralizing HNN extensions `G *_C (C × Z)` and the doubles `G *_C G` over
subgroups `C` with decidable membership would lie in `B_A`. Their word problems are
solvable exactly when membership in `C` is decidable
(`bh-embeddability-forces-decidable-edge-membership`, part (i)).

## First test cases

The test cases recorded on the refuted node all have decidable stabilizers, so they
are test cases of this claim:
- `Z wr_(F_2/⟨a⟩) F_2`, with infinite cyclic stabilizers. **Settled (2026-09-18):** `⟨a⟩ = C_(F_2)(a)`, so
  case 2 of `pbh-coset-wreaths-iff-identity-edge-hnns` applies. More generally, every
  finitely generated stabilizer in a free top group is covered by
  `free-group-coset-wreaths-satisfy-pbh`;
- `Z wr_X PSL_2(Z[1/2])` over `X = PSL_2(Z)\PSL_2(Z[1/2])`
  (`z-wr-psl2-z-half-embeds-in-fp-self-similar-group`). **Settled in `B_A` (2026-09-18,
  lane bh-openq-papers):** `lamp-wreaths-over-psl2-tree-vertices-lie-in-b-a` and
  `wreaths-over-clopen-stabilizer-cosets-lie-in-b-a` realize the coset space through
  clopen stabilizers. With the criterion of `free-permutational-products-preserve-pbh`,
  this also puts the double `PSL_2(Z[1/2]) *_(PSL_2(Z)) PSL_2(Z[1/2])` and its
  centralizing HNN extensions in `B_A` (`double-of-psl2-z-half-along-psl2-z-lies-in-b-a`).
  The self-similar form of the question stays open.

## Reductions

- **One orbit is enough.** `A wr_(X_1 ⊔ X_2) G` embeds diagonally in
  `(A wr_(X_1) G) × (A wr_(X_2) G)`, via `(f_1 f_2, g) -> ((f_1, g), (f_2, g))`, and `B_A`
  is closed under finite products. So the claim reduces to `X = G/C`.
- **Equivalent forms** (`pbh-coset-wreaths-iff-identity-edge-hnns`). For one orbit
  `G/C`, the claim for all `A` is equivalent to each of:
  - `Z/2 wr_(G/C) G ∈ B_A`;
  - the identity-edge HNN extension `G *_C (C × Z) ∈ B_A`;
  - `C = C_G(m)` for some element `m` of some `B_A`-overgroup of `G`.

  So this claim is equivalent to the permutational form of the identity-edge case of
  `bh-embeddability-survives-decidable-edge-hnn`, and to the realization of every
  decidable subgroup as a centralizer in an overgroup. That node lists the subgroups
  already covered: finite subgroups, centralizers of finite sets, retracts, fixed
  subgroups of automorphisms with mapping torus in `B_A`, and finite intersections of
  these.
