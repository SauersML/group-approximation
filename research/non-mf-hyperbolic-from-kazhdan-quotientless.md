---
rg: 2
id: non-mf-hyperbolic-from-kazhdan-quotientless
kind: route
title: A hyperbolic Kazhdan group without finite quotients is a non-MF hyperbolic group
target: non-mf-hyperbolic-group
requires:
  - kazhdan-hyperbolic-group-without-finite-quotients
  - mf-kazhdan-group-without-finite-quotients-is-trivial
---

Assume `mf-kazhdan-group-without-finite-quotients-is-trivial`. Let `G` be the
infinite hyperbolic Kazhdan group supplied by the other prerequisite. If `G`
were operator MF, the first assumption would force `G=1`, contradicting
infinitude. Hence `G` is a word-hyperbolic group that is not MF.

This is a conditional implication. The 2026-09-11 audit
`mf-to-weak-qd-citation-has-unproved-lifting-step` invalidates the old
Ozawa--Thom justification for the first prerequisite: its actual theorem
assumes weak quasidiagonality, with completely positive approximations.
