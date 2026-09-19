---
rg: 2
id: boone-halting-subgroup-is-normal-closure
kind: claim
title: Simpson's Lemma 7 - the halting subgroup of the tower is the normal closure of t
distinct_from:
  boone-tower-good-subgroup-transport: That says the halting subgroup meets the base group correctly at every stage, a goodness statement proved by transport; this identifies the whole subgroup it generates in the tower with the normal closure of a single element, by induction on halting computations.
  boone-normal-closure-of-t-finitely-generated: That is a finite-generation statement about the same subgroup, needed only for finite presentability; this identifies which subgroup it is, and neither implies the other.
  finite-infranormal-subgroup-is-normal: That is a general fact about infranormal subgroups in the compression lane; this is one identification inside the Boone tower and has no infranormality in it.
artifacts:
  - GroupApproximation/Computability/BooneGroupModularMachine.lean
  - GroupApproximation/Computability/BooneGroupMachineIndex.lean
  - GroupApproximation/Computability/BooneGroupGoodness.lean
---

ESTABLISHED (2026-08-16), `BooneGroupGoodness.towerSub_halting_eq_towerTSub`.
Item **S6** of the roadmap in `Computability/BooneGroupBase`.  In the tower
`G'_M` of a modular machine,

    T'_M  =  <<t>>,

the normal closure of the single generator `t`.  Simpson's Lemma 7.

## How it was proved, against how it was planned

The plan was an induction on the length of the halting computation via
`Relation.ReflTransGen.head_induction_on`, with the displayed computation
`r_i^{-1} t(a,b) r_i = t(a1,b1)` as the step.  The step is real and is
`stable_conj_emb_right` / `_left`: the stable letter attached to a quadruple
carries the source embedding onto the target,
`of (emb c 0 M^2 1 g) = t * of (emb a b M M g) * t^{-1}`, which is the defining
relation of the HNN extension read through `quadEquiv` -- and `quadEquiv` was
defined to make it so.

What the finished proof does *not* do is string those steps along a computation
by hand.  Both inclusions are structural inductions over the identification
list instead (`towerSub_le_of_mem` with `twSub_halting_le_comap` one way,
`towerTSub_le_towerSub_halting` with `hasLetters_towerTSub` the other), which
is the same shape as `towerSub_inf_range` one level down.  The machine enters
only through the step above, so no new machine input was needed, as the plan
predicted.

## Where it is consumed

Together with [[boone-tower-good-subgroup-transport]] it is what turns the
halting set into a *subgroup-theoretic* condition, which the final stable
letter of [[boone-commutator-criterion-for-halting]] then converts into a
commutator equation.
