---
rg: 2
id: rokhlin-maximality-on-tester-covers-every-group
kind: route
title: Subgroup and colimit closure let the tester host decide Rokhlin maximality for every group
target: bernoulli-rokhlin-entropy-maximal-for-every-group
requires:
  - bernoulli-rokhlin-entropy-maximal-on-fixed-tester
  - bernoulli-rokhlin-maximality-passes-to-subgroups
  - bernoulli-rokhlin-deficit-has-a-finitary-witness
  - universal-all-group-subgroup-colimit-class-tester
artifacts:
  - research/artifacts/gottschalk-rokhlin-entropy-route-2026-09-12.md
---

Fix `q`. Let `C_q` be the class of groups whose finitely generated subgroups are
all Rokhlin-maximal at `q`.

* `C_q` is closed under subgroups.
* `C_q` is closed under directed colimits with arbitrary structure maps, by the
  finitary-witness claim: a finitely generated subgroup of a colimit is a directed
  colimit of finitely generated subgroups of the stages.
* For countable `G`, membership in `C_q` is Rokhlin-maximality of `G` itself. This
  follows from the subgroup claim and colimit closure along finitely generated
  subgroups.

The tester theorem turns `U in C_q` into membership of every group.

This route and `rokhlin-maximality-for-every-group-covers-tester` record an
equivalence. The dependency cycle they form is intended.
