---
rg: 2
id: boone-hnn-tower-embeds-base-group-proof
kind: route
title: Bundle carrier, instance and embedding into one stage, then fold
target: boone-hnn-tower-embeds-base-group
requires: [boone-base-group-and-lemma-five]
artifacts:
  - GroupApproximation/Computability/BooneGroupTower.lean
---

## Why sufficient

`Stage.step S psi` forms `HNNExtension S.carrier A B psi` and takes the new
embedding to be `HNNExtension.of` composed with the old one; its injectivity
field is `HNNExtension.of_injective` composed with the previous stage's, so the
invariant is re-established at each step with no separate argument.  `tower` is
`List.foldl` of that, `Stage.base` is the base group with the identity
embedding, and `tower_i_injective` is an induction over the list whose step is
precisely the field just described.

The prerequisite is used for the identifications, not for the fold.  Both
`G_{ab}^{MM}` and `G_{c0}^{M^2,1}` are ranges of embeddings of the base group,
so `MonoidHom.ofInjective` -- available because `emb_injective` holds for
nonzero parameters -- makes each isomorphic to the base group, and `quadEquiv`
is the composite of one isomorphism with the inverse of the other.  Without
injectivity of `emb` there is no identification to adjoin.

`machineIdentifications` collects one `quadIdentification` per residue pair
carrying a quadruple, over the list `residuePairs mm` (`mem_residuePairs`
records that every pair below the modulus occurs), and `machineTower` is
`tower` of that list.  The hypothesis `(mm.size : Z) != 0` is what
`emb_injective` needs, and `pow_ne_zero 2` supplies it on the target side.

## Not a restatement

The prerequisite says nothing about HNN extensions; this claim is a
construction that does not exist without one, and its content -- that
injectivity survives the whole fold -- is about the tower rather than about the
base group.
