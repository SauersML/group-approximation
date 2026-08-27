---
rg: 2
id: hyperlinear-implies-sofic
kind: claim
title: "Every hyperlinear group is sofic (affirmative answer to Question 3.4)"
distinct_from:
  sofic-implies-hyperlinear: that is the converse implication, formalized and established; this is the open direction
  hyperlinear-nonsofic-group: that is the literal negation of this claim — the separation answer to Q3.4; establishing either forecloses the other
---

The affirmative answer to Pestov's Question 3.4: hyperlinearity implies
soficity for groups, i.e. the two approximation classes coincide (the converse,
sofic-implies-hyperlinear, is formalized). Equivalently, by contraposition:
every nonsofic group is non-hyperlinear.

**Payoff.** Nonsofic groups now exist unconditionally --- first
openai-leavitt-unit-nonsofic (2026-08-01), then the later constructions that
build on it, and independently universal-leavitt-el4-nonsofic here --- so this
claim would immediately produce an
explicit non-hyperlinear group — see the route
non-hyperlinear-from-hyperlinear-implies-sofic into non-hyperlinear-group.
That makes the affirmative answer at least as strong as the program's other
root target, not a consolation outcome.

**What it would take.** A general theorem converting hyperlinear
approximations (asymptotic homomorphisms into unitaries with the normalized
Hilbert–Schmidt metric) into sofic approximations (into permutations with the
Hamming metric), for arbitrary groups. No such technique exists. The caution
of notes/OBSTRUCTIONS.md §5 applies with full force: proving particular
candidates non-hyperlinear (e.g. kt-pair-non-hyperlinear-rigidity) removes
candidates one at a time and can never establish this universal statement.
