---
rg: 2
id: pestov-question-5-3-negative-proof
kind: route
title: A near action would make the group sofic
target: pestov-question-5-3-negative
requires: [universal-leavitt-el4-nonsofic]
artifacts:
  - GroupApproximation/Endpoint/MainResults.lean
---

## Why sufficient

One implication and one contradiction.  `isSofic_of_admitsEssentiallyFreeNearAction`
says a group admitting an essentially free, measure-preserving near action on a
set with a finitely additive probability measure on its full power set is
sofic.  The prerequisite says the ambient group of Theorem A is not.  So it
admits no such near action
(`universalLeavittEL4_not_admitsEssentiallyFreeNearAction`), and it is
countable, which is what the question asks for.

## Not a restatement

The prerequisite is about approximation by finite permutations; the target is
about the nonexistence of a class of measure-preserving actions.  They are
connected by the Elek--Szabo implication, which is the content of the step and
is a theorem in its own right -- the target would be open, not restated, if
that implication were unavailable.
