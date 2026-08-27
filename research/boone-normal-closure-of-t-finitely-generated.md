---
rg: 2
id: boone-normal-closure-of-t-finitely-generated
kind: claim
title: The associated subgroups of the Boone tower are finitely generated
distinct_from:
  hnn-extension-finite-presentation-permanence: That is the generic permanence statement whose hypothesis this claim discharges for one tower; it is about presentations, this is about generation.
  infranormal-compact-closure-normal: That is a statement about infranormal subgroups and compact images in the compression lane; this is finite generation of two explicit subgroups of an HNN tower.
artifacts:
  - GroupApproximation/Computability/BooneGroupBase.lean
  - GroupApproximation/Computability/BooneGroupTower.lean
---

ESTABLISHED (2026-08-16), `Computability/BooneGroupFinitePresentation`
(`Gsub_fg`, `liftedSubgroup_fg`, `towerTSub_fg`).  Two finite-generation facts
are needed before finite presentability of the final group can even be stated
through [[hnn-extension-finite-presentation-permanence]]:

* each `G_{ab}^{MN}` is finitely generated -- immediate from
  `Gsub_eq_closure`, which exhibits it as `<t(a,b), x^M, y^N>`, so this half is
  a corollary of [[boone-base-group-and-lemma-five]] rather than new work;
* the normal closure `<<t>>` of the last stage, which is the associated
  subgroup of the final stable letter `k`, is finitely generated **as a
  subgroup**.  That is the substantive half: `<<t>>` is not finitely generated
  in the base group -- it is free of infinite rank there, on the family
  `t(a,b)` -- so the finite generation has to come from the stable letters of
  the tower conjugating those basis elements onto one another.

The second half is what makes this a claim rather than a remark: it is a
statement about the tower, and it is false one level down.  What makes it true
upstairs is that `liftedSubgroup φ A = ⟨of '' A, t⟩`, so each stage costs
exactly **one** new generator; along a machine's finite identification list
that is finitely many in total.
