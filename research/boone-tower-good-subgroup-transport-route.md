---
rg: 2
id: boone-tower-good-subgroup-transport-route
kind: route
title: Rewrite the parameter-set images along the associated isomorphism, then iterate up the tower
target: boone-tower-good-subgroup-transport
requires: [hnn-good-subgroup-lemma, boone-halting-index-good-parameter-set, boone-hnn-tower-embeds-base-group]
artifacts:
  - GroupApproximation/Computability/BooneGroupMachineIndex.lean
  - GroupApproximation/Computability/BooneGroupTower.lean
---

## Why sufficient

The three prerequisites are the three distinct things this needs: the lemma,
the index computation it is applied to, and the tower it is applied in.

**Goodness at one stable letter.**  The good-subgroup condition asks for
`phi (T_M cap Asub) = T_M cap Bsub`, where `Asub = G_{ab}^{MM}` and
`Bsub = G_{c0}^{M^2,1}` and `phi = quadEquiv`, which is
`emb c 0 M^2 1` after `(emb a b M M)^{-1}`.  The second prerequisite already
exhibits both sides as the images of one and the same parameter set
`haltParams a b` under the two embeddings (`twSub_halting_inf_Gsub_src`,
`twSub_halting_inf_Gsub_right`, `_left`).  So the condition is these two image
computations composed with the definition of `quadEquiv` -- a rewrite, with
`emb_injective` making the inverse well defined.  The same argument with the
full index set in place of `haltingSetZ` handles `T`.

**Up the tower.**  With goodness available at a stage, the first prerequisite
gives `T'_n cap of.range = T_n.map of` at that stage.  The third prerequisite
provides the stage-by-stage construction with its embedding invariant, so the
conclusion at stage `n` is exactly the goodness hypothesis needed at stage
`n+1`, and the induction is over the list `machineIdentifications mm`.  This
stagewise assembly is forced by Mathlib carrying one stable letter per
`HNNExtension`, and it is the only reason the statement is not a single
application of the lemma.

## Not a restatement

Each prerequisite fails to imply the target on its own in an identifiable way:
the lemma is about an arbitrary good subgroup and does not know that `T_M` is
one; the index computation is about the base group and never leaves it; the
tower is a construction with no correctness statement attached.
