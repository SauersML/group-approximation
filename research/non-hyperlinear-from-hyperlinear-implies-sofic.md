---
rg: 2
id: non-hyperlinear-from-hyperlinear-implies-sofic
kind: route
title: Non-hyperlinear group from the affirmative answer to Q3.4
target: non-hyperlinear-group
requires:
  - hyperlinear-implies-sofic
  - openai-leavitt-unit-nonsofic
---

# Non-hyperlinear group from the affirmative answer to Q3.4

Contraposition plus an explicit witness. If every hyperlinear group is sofic
(hyperlinear-implies-sofic), then every nonsofic group is non-hyperlinear; the
Kun--Thom wreath products (kun-thom-nonsofic-wreath, Theorems A and E of
arXiv:2608.06222) are explicit nonsofic groups, so any one of them — e.g.
`(Z/2Z) wr_(G/Gamma) G` for the Theorem E pair — would be an explicit
non-hyperlinear group.

This route records why the affirmative answer to Q3.4 is not a consolation
outcome for this program: it would establish the other root target outright.

**Witness (2026-08-21 repair).**  The witness slot now consumes
`openai-leavitt-unit-nonsofic`, which this repository establishes through
its own kernel-checked endpoint (`universal-leavitt-el4-nonsofic`); the
Kun--Thom wreath products remain a second explicit family of nonsofic
groups, but they rest on an unrefereed preprint import and must not be the
sole witness on a route into the goal.  Both witnesses are finitely
generated, so any finite-generation side condition on
`hyperlinear-implies-sofic` is met.
