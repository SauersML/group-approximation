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

ESTABLISHED (2026-08-16),
`Computability/BooneGroupFinitePresentation.finalGroup_isFinitelyPresented`.
Item **S8** of the roadmap in `Computability/BooneGroupBase`: the group `G_M`
-- the tower over the base group with the final stable letter `k` adjoined --
is finitely presented, for every modular machine.

**Status (2026-08-16): the permanence statement and both finite-generation
facts are proved**, so what this claim needs is in hand; see the route below
and `Computability/BooneGroupFinitePresentation`.

## Why it is not automatic

The base group is presented, and that half is done
([[boone-base-group-two-generator-one-relator]]).  Each stage adds one stable
letter, and a *finite* machine contributes finitely many of them.  What is
missing is the permanence statement itself,
[[hnn-extension-finite-presentation-permanence]], together with finite
generation of the associated subgroups
([[boone-normal-closure-of-t-finitely-generated]]) without which the
permanence statement does not apply.

The estimate here was 500--900 lines, most of it in the permanence statement.
It came to about 300, because the permanence statement does not need Britton's
Lemma: Mathlib *defines* the HNN extension as a quotient of `G ∗ Z`, so the
only content is cutting the relation family down to a generating set.  The
prediction that this item carried no mathematical risk was right.

## What it is needed for

Only for the word *presented* in the conclusion.  The halting biconditional
[[boone-commutator-criterion-for-halting]] holds without it, and everything
about correctness of the tower is independent of it.
