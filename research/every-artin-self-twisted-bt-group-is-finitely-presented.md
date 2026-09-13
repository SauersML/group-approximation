---
rg: 2
id: every-artin-self-twisted-bt-group-is-finitely-presented
kind: claim
title: For every Artin group A the twisted Brin-Thompson group AV_A is finitely presented
refuted_by:
  - self-twisted-bt-group-of-infinite-group-is-not-fp
distinct_from:
  self-twisted-bt-group-of-infinite-group-is-not-fp: that is the established theorem refuting this claim, for every infinite group; this is the refuted premise, kept so that the dead route through it stays visible.
---

**REFUTED** by `self-twisted-bt-group-of-infinite-group-is-not-fp`.

The claim: for every Artin group `A` on a nonempty generating set, the twisted
Brin–Thompson group `AV_A`, for the translation action, is finitely presented. If it
were true, `AV_A` would be its own finitely presented host, answering Zaremsky
Problem 3.8 yes. That is the route `artin-twisted-bt-fp-host-via-own-finite-presentation`.

## Attempts

- Refuted. The translation action has infinitely many orbits of two-element subsets,
  so Zaremsky's criterion (arXiv:2405.18354) fails. Any finitely presented host of
  `AV_A` must be a proper overgroup.
