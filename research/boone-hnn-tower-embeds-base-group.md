---
rg: 2
id: boone-hnn-tower-embeds-base-group
kind: claim
title: The HNN tower of a modular machine exists and embeds the base group
distinct_from:
  boone-base-group-and-lemma-five: That claim is about the base group and its subgroups; this one builds the iterated HNN extension over it, one stable letter per residue pair, and says the base group survives inside.
artifacts:
  - GroupApproximation/Computability/BooneGroupTower.lean
  - GroupApproximation/Computability/BooneGroupModularMachine.lean
---

ESTABLISHED, as a construction.  Simpson's Definition 6 builds `G'_M` from the
base group by adjoining one stable letter per machine quadruple, each
conjugating a copy of `G_{ab}^{MM}` onto a copy of `G_{c0}^{M^2,1}`.  Mathlib's
`HNNExtension` carries one stable letter, so the tower is built one letter at a
time, and

* `tower : List Identification -> Stage` is the fold, with
  `tower_i_injective` maintaining injectivity of the composite embedding of the
  base group as a *loop invariant* rather than proving it afterwards;
* `machineTower mm hM` is the tower of an actual modular machine -- one
  identification for each residue pair carrying a quadruple, indexed by
  `residuePairs mm` -- and `machineTower_i_injective` is its embedding
  statement;
* `quadEquiv a b c M hM : G_{ab}^{MM} =~ G_{c0}^{M^2,1}` is the identification a
  quadruple contributes, i.e. Simpson's `phi_i`.

## The construction problem this solves

Writing the tower as a recursive *type* does not work directly: each stage's
associated subgroups live in the previous stage, so the type, its group
instance and the embedding of the base group would all have to be defined by
one mutual recursion.  Bundling avoids it entirely.  A `Stage` carries the
carrier, its group structure, the map `i` from the base group, and the proof
that `i` is injective; `Stage.step` is then an ordinary function on bundles and
the tower is a fold.

Residue pairs carrying no quadruple contribute nothing, which is the same as
contributing trivial associated subgroups -- an HNN extension with trivial
associated subgroups is a free product with `Z`, which is harmless.

## What is not claimed

Correctness of the tower is *not* part of this claim.  That the halting set
becomes a good subgroup, and that the resulting group has the halting
biconditional, are [[boone-tower-good-subgroup-transport]] and
[[boone-commutator-criterion-for-halting]], both open, and both resting on
[[hnn-good-subgroup-lemma]], which is where Britton's Lemma enters.
