---
rg: 2
id: boone-base-group-two-generator-one-relator
kind: claim
title: The split-extension base group is the three-generator one-relator group of the source
distinct_from:
  boone-base-group-and-lemma-five: That claim is about the subgroups of the split extension and Simpson's Lemma 5; this one says the split extension is presented by generators and relations, which those subgroup statements neither use nor imply.
artifacts:
  - GroupApproximation/Computability/BooneGroupPresentation.lean
---

ESTABLISHED.  `Computability.BooneGroupPresentation.presentedEquiv`:

    PresentedGroup {x y x^{-1} y^{-1}}  isomorphic-to  BaseGroup

on three generators `t, x, y` with the single commutator relator.  So the
model taken as the *definition* in [[boone-base-group-and-lemma-five]] is
Simpson's `G = <t, x, y | xy = yx>` and not merely a group with the same
properties.

## Why the chain needs it, and only here

Nothing about the correctness of the Novikov--Boone tower uses the
presentation: the good-subgroup lemma, the halting biconditional and every
index computation are statements about subgroups and are proved in the split
extension.  The presentation is needed for one purpose only -- calling the
final group *finitely presented*, which is what
[[boone-final-group-finitely-presented]] has to establish and which the word
problem statement is about.  This is the deferred cost of modelling `G` as a
split extension in order to avoid the Kurosh subgroup theorem.
