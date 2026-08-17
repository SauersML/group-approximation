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
---

OPEN.  Item **S6** of the roadmap in `Computability/BooneGroupBase`.  In the
tower `G'_M` of a modular machine,

    T'_M  =  <<t>>,

the normal closure of the single generator `t`.  Simpson's Lemma 7.

## The route, and why it is not merely a sketch

Induction on the length of the halting computation, via
`Relation.ReflTransGen.head_induction_on`.  The inductive step is the displayed
computation of the source, `r_i^{-1} t(a,b) r_i = t(a1,b1)`, where `r_i` is the
stable letter attached to the quadruple that fires at `(a,b)`; at the level of
basis indices that identity is `haltsZ_right_iff` -- the machine fact of
[[modular-machine-halting-invariance]] -- again, so no new machine input is
needed.

Estimated cost: about 150 new lines.  No route node is recorded for it yet:
the induction has been read but not re-derived against Mathlib's HNN API, and
a route in this graph asserts that its implication is valid, not that it is
plausible.

## Where it is consumed

Together with [[boone-tower-good-subgroup-transport]] it is what turns the
halting set into a *subgroup-theoretic* condition, which the final stable
letter of [[boone-commutator-criterion-for-halting]] then converts into a
commutator equation.
