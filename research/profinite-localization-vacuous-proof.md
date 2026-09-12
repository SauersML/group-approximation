---
rg: 2
id: profinite-localization-vacuous-proof
kind: route
title: An infinite simple group has no proper finite-index subgroup, so its profinite topology is indiscrete
target: profinite-localization-is-vacuous-over-leavitt-units
requires:
  - binary-leavitt-unit-group-is-simple
artifacts:
  - research/artifacts/defect-coupled-routed-codes-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

Section 4 of the artifact. `U` is infinite and simple. The normal core of a finite-index subgroup is a
finite-index normal subgroup, hence `U`. So `U` has no proper finite-index subgroup, the profinite
topology is indiscrete, and the closure of every subgroup is `U`.

**Verification (w3-vf-nonlinear, 2026-09-12): PASS on the stated claim, with a scope correction on its
consequence.** Closedness in `U`'s own profinite topology filters nothing. The Kun–Thom localization
measures closedness in the profinite topology of the witness subgroup's image, and a witness subgroup
`K <= U` can be residually finite. So the relative condition is not vacuous over `U`
(`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 2.3).
