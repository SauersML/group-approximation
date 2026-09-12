---
rg: 2
id: fp-surjunctive-nonsofic-double-by-stable-k2
kind: route
title: Kill the full stable-rank Laurent kernel and fold the finitely presented double
target: fp-surjunctive-nonsofic-group-exists
requires:
  - graph-folds-over-surjunctive-groups-are-surjunctive
  - steinberg-finite-presentation-and-kazhdan-theorem
  - kt-pair-group-double-is-nonsofic
  - kun-thom-nonsofic-wreath
  - residually-finite-groups-are-surjunctive
artifacts:
  - research/artifacts/fp-surjunctive-nonsofic-double-2026-09-11.md
---

The artifact fixes `q=2`, matrix rank six, and three Laurent
variables. Classical dimension-three K2 stability and the regular
Laurent fundamental theorem identify the entire finite-rank kernel
as `Z^3`. Three kernel relators therefore produce a finitely
presented elementary group from the Steinberg source.

Its semidirect product with the finitely presented `SL_3(Z)` is
finitely presented. The positive polynomial elementary subgroup
is finitely generated explicitly by elementary matrices whose
coefficients are one or one of the three variables. Gluing two
finite actor presentations along those finitely many generators
gives a finite presentation of the double.

Kun--Thom Theorem E makes the actor residually finite, hence
surjunctive. The fold is injective on each vertex group, so the
graph-of-groups theorem makes the double surjunctive. Kun--Thom
Theorem A makes this same double nonsofic. All stability bounds,
kernel identifications, and finite-presentation steps are
specified in the linked proof.
