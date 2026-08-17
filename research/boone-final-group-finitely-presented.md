---
rg: 2
id: boone-final-group-finitely-presented
kind: claim
title: The final group of the Boone tower is finitely presented
distinct_from:
  novikov-boone-fp-group-undecidable-word-problem: That is the undecidability statement, which needs this claim plus the halting biconditional plus a machine with non-computable halting set; this is only the adjective "finitely presented", and carries no decision problem.
  boone-hnn-tower-embeds-base-group: That is the construction of the tower and its embedding invariant, which holds whether or not any stage is finitely presented; this is a presentation-theoretic statement about the finished group.
  boone-normal-closure-of-t-finitely-generated: That is finite GENERATION of the associated subgroups, a prerequisite here; this is finite PRESENTATION of the whole group, and the gap between them is the permanence statement.
  hnn-extension-finite-presentation-permanence: That is the generic permanence statement for an arbitrary HNN extension; this is its application to one tower, which additionally needs the base presentation and finite generation of each associated subgroup.
  finitely-presented-sofic-non-mf: That is about the manuscript's group E and packages soficity with failure of MF; this is about the Boone tower of a modular machine and asserts only finite presentability.
artifacts:
  - GroupApproximation/Computability/BooneGroupPresentation.lean
  - GroupApproximation/Computability/BooneGroupTower.lean
---

OPEN.  Item **S8** of the roadmap in `Computability/BooneGroupBase`, and the
larger of the two remaining bookkeeping items: the group `(G'_M)'` -- the tower
over the base group with the final stable letter `k` adjoined -- is finitely
presented.

## Why it is not automatic

The base group is presented, and that half is done
([[boone-base-group-two-generator-one-relator]]).  Each stage adds one stable
letter, and a *finite* machine contributes finitely many of them.  What is
missing is the permanence statement itself,
[[hnn-extension-finite-presentation-permanence]], together with finite
generation of the associated subgroups
([[boone-normal-closure-of-t-finitely-generated]]) without which the
permanence statement does not apply.

Estimated cost: 500--900 new lines, most of it in the permanence statement.
This and the good-subgroup lemma are the two load-bearing items left in the
chain, and unlike the good-subgroup lemma this one carries no mathematical
risk -- only length.

## What it is needed for

Only for the word *presented* in the conclusion.  The halting biconditional
[[boone-commutator-criterion-for-halting]] holds without it, and everything
about correctness of the tower is independent of it.
