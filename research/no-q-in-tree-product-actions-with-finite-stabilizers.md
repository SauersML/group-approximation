---
rg: 2
id: no-q-in-tree-product-actions-with-finite-stabilizers
kind: claim
title: A group acting on a finite product of trees with finite vertex stabilizers contains no copy of (Q,+), so no discrete subgroup of Aut(T_1) x ... x Aut(T_r) contains GL_n(Q), Aff(Q) or U_3(Q)
distinct_from:
  divisible-elements-act-elliptically-on-trees: that is the one-tree dichotomy (fixed vertex or parabolic at one end); this is its consequence under finite stabilizers, for products of trees, and it excludes a named host class.
  gl-n-q-embeds-in-fp-simple-group: that is the open embedding problem; this excludes Burger-Mozes type lattices as hosts.
  proper-semisimple-cat0-groups-contain-no-gl-2-q: that excludes GL_n(Q), Aff(Q) and U_3(Q) from groups acting properly by semisimple isometries on CAT(0) spaces, by distortion; this excludes (Q,+) itself, by divisibility, and needs only finite vertex stabilizers on a product of trees that need not be locally finite, with no properness.
---

**ESTABLISHED** through `no-q-in-tree-product-actions-with-finite-stabilizers-proof`.
Not independently reviewed. Elementary; no priority is claimed.

## Statement

Let `T_1, ..., T_r` be simplicial trees and `X = T_1 x ... x T_r`. Let a group `H`
act on `X` preserving the product structure: each element maps every factor
isomorphically onto a factor. Suppose the stabilizer in `H` of every vertex of `X`
is finite. Then `H` contains no subgroup isomorphic to `(Q,+)`.

Hence `H` contains none of `GL_n(Q)`, `SL_n(Q)`, `PGL_n(Q)` (`n >= 2`), `Aff(Q)`,
`B_2(Q)`, `U_3(Q)`, nor any group containing `(Q,+)`.

## Host classes excluded

- **Discrete groups.** Let the `T_i` be locally finite, and let `Γ` be a discrete
  subgroup of `Aut(T_1) x ... x Aut(T_r)`, possibly extended by factor
  permutations. Its vertex stabilizers are discrete intersected with compact,
  hence finite, so `Γ` satisfies the hypothesis.
- **Burger–Mozes groups.** This covers the Burger–Mozes finitely presented simple
  groups. They are cocompact lattices in `Aut(T_1) x Aut(T_2)` (Burger–Mozes,
  *Lattices in product of trees*, Publ. IHES 92 (2000)). The survey
  arXiv:2306.16356v3 §4.1 names them, with the Caprace–Rémy groups, as arguably the
  only known infinite finitely presented simple groups not of Thompson type. The
  same holds for Wise's lattices and every lattice in a product of two locally
  finite trees. `research/artifacts/gq-reform-countable-ladder.md` already
  excludes the cocompact ones as CAT(0) groups. This node drops cocompactness,
  and discreteness too, keeping only finite vertex stabilizers.
- **One tree.** For `r = 1`: groups acting on a tree with finite vertex
  stabilizers, for example virtually free groups.

So none of these can be the finitely presented simple host for
`gl-n-q-embeds-in-fp-simple-group`, nor for its stepping stones.

## Relation to the distortion obstruction

For lattices in products of locally finite trees, the exclusion of `GL_n(Q)`,
`Aff(Q)` and `U_3(Q)` already follows from
`proper-semisimple-cat0-groups-contain-no-gl-2-q`, by distortion of
`BS(1,2) <= GL_2(Q)`. That node also covers Caprace–Rémy lattices through
Bridson and Haglund. What is new here:

- `(Q,+)` itself, and every group containing it (`Q^n`, divisible nilpotent
  groups), is excluded. Distortion says nothing about these.
- Trees need not be locally finite and the action need not be metrically proper.
  Only finite vertex stabilizers are needed, for example free actions on trees
  of infinite valence.

## Attempts

1. Extending the divisibility argument to CAT(0) polyhedral complexes was not
   pursued. For the groups of the root it is superseded by the distortion node.
