---
rg: 2
id: type-a-actors-split-only-over-orbit-finite-edges
kind: claim
title: If a group acts with finitely generated point stabilizers and finitely many orbits of two-element subsets, every vertex and edge stabilizer of an irreducible tree action has finitely many orbits, and every point stabilizer acts cocompactly on the whole tree
distinct_from:
  type-a-actors-have-no-infinite-virtually-central-subgroup: that is a necessary condition on the actor coming from finite-index centralizers, with no tree in sight; this is a necessary condition coming from any irreducible action of the actor on a tree, and it constrains the edge and vertex groups of every splitting.
  stable-permutation-hnn-of-type-a-actor-is-type-a: that is a sufficient condition, building a type (A) HNN extension when the edge group already has finitely many orbits; this shows that condition is necessary for every type (A) action of any non-ascending HNN extension or non-degenerate amalgam.
  bh-embeddability-survives-decidable-edge-hnn: that is the open permanence claim; this constrains one engine for it, type (A) actions of the HNN extension itself (its Attempt 5), and leaves host engines untouched.
  closed-mcg-pair-orbit-finite-actions-have-large-stabilizers: that constrains stabilizers of pair-orbit-finite actions of mapping class groups through curves; this constrains stabilizers and orbit counts through actions on trees.
---

**ESTABLISHED** through `type-a-actors-split-only-over-orbit-finite-edges-proof`.
The proof is elementary apart from two textbook facts from Serre, *Trees*
(§I.6.4 axes of hyperbolic automorphisms; §I.6.5 a finitely generated group of
elliptic automorphisms fixes a vertex). No novelty is claimed for the tree
lemmas; the orbit-count consequence is not recorded elsewhere in this graph.

## Statement

Let `G` be a finitely generated group acting on a set `X` such that

- every point stabilizer `P_x = Stab_G(x)` is finitely generated, and
- there are finitely many `G`-orbits of two-element subsets of `X`.

Let `G` also act without inversions on a simplicial tree `T`. Assume the tree
action is **irreducible**: it is minimal (no proper `G`-invariant subtree), it
has no global fixed vertex, and no end of `T` is `G`-invariant. Then:

1. **Cocompact stabilizers.** For every `x in X`, `P_x` contains a hyperbolic
   element, the convex hull of the axes of its hyperbolic elements is all of
   `T`, and `P_x \ T` is a finite graph. So `P_x` is the fundamental group of a
   finite graph of groups with vertex groups `P_x ∩ G_v`.
2. **Orbit-finite stabilizers.** For every vertex `v` and every edge `e` of `T`,
   the stabilizers `G_v` and `G_e` have finitely many orbits on `X`.

Faithfulness and finite presentation are not used. So (1) and (2) hold for every
action of type (A) (`type-a-action-gives-boone-higman-for-subgroups`) and for
every type [A_2] action with kernel (`boone-higman-implies-relative-permutational-bh`).

## Irreducible Bass--Serre trees

The proof route also checks the standard fact that the Bass--Serre tree is
irreducible in two cases:

- `A *_C B` with `C != A` and `C != B`;
- `A *_phi` with `phi : C_1 -> C_2`, `C_1 != A` and `C_2 != A` (non-ascending).

For these splittings, (2) says `A`, `B`, `C` (respectively `A`, `C_1`, `C_2`)
all have finitely many orbits on `X`.

## What it changes

- **Attempt 5 of `bh-embeddability-survives-decidable-edge-hnn`.** That attempt
  showed only that a point stabilizer of a type (A) action of `K = A*_phi` fixes
  no vertex. For non-ascending `K`, (1) and (2) are far stronger: every point
  stabilizer is cocompact on the whole Bass--Serre tree, and the edge group
  `C_1` must itself have finitely many orbits. The consequences that kill the
  engine on concrete inputs are in
  `type-a-actors-have-no-proper-power-cyclic-edge-splittings`.
- **Necessity in the stable-permutation construction.** In
  `stable-permutation-hnn-of-type-a-actor-is-type-a` the clause "`D_1` has
  finitely many orbits on `X`" was a hypothesis of the construction. By (2) it
  is forced for every type (A) action of a non-ascending HNN extension on any
  set, so no variant of that construction can drop it.
- **Sanity checks.**
  - Thompson's `F` acts of type (A) on dyadic points of `(0,1)`. Its only
    splittings are ascending, which the hypotheses exclude.
  - For `F_2 = Z * Z` the edge group is trivial, so (2) forces `X` finite. This
    agrees with the classical fact that a finitely generated infinite-index
    subgroup `H` of a free group has infinitely many double cosets `H\F/H`.
  - `PSL_2(Z) = Z/2 * Z/3` on `P^1(Q)` has infinitely many orbits of pairs, as
    it must.
