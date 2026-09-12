---
rg: 2
id: jacobson-finite-field-coset-phase-proof
kind: route
title: Use finite-field coset distances to construct an exact-base centralizer obstruction
target: jacobson-corona-centralizer-does-not-lift-to-base-commutants
requires:
  - jacobson-coherent-group-is-an-ascending-corner-extension
  - jacobson-shift-literal-quotient-is-laurent-times-z
  - jacobson-coherent-quotient-is-faithful-and-has-mf-dichotomy
artifacts:
  - research/artifacts/jacobson-corona-centralizer-does-not-lift-to-base-commutants-2026-09-08.md
---

Evaluate the Laurent base onto `SL_3(F_(2^n))`. The graph on left
constant-group cosets, with edges supplied by all representatives and
the mixed involution, is connected with degree at most `168` and
unbounded radius. Phases varying linearly with distance commute with
constants exactly and have mixed-involution commutator at most
`pi/radius`.

Every matrix in the full regular-image commutant has constant diagonal;
the constructed phases attain both `1` and `-1`, giving distance
exactly one from that algebra. Laurent polynomial separation and
geodesic phase values prove faithfulness on the quotient times `Z`.
Finite-packet averaging estimates and the precise head-killing scope
are verified explicitly.
