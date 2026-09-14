---
rg: 2
id: profinite-localization-is-vacuous-over-leavitt-units
kind: claim
title: Every proper subgroup of the binary Leavitt unit group is non-closed in its profinite topology
distinct_from:
  kun-thom-wreath-deficit-witnesses-need-nonclosed-stabilizers: that localizes Bernoulli deficit witnesses over a wreath with residually finite actor to non-closed stabilizers, a genuine restriction there; this shows the analogous condition over the Leavitt units holds for every proper subgroup and so filters nothing.
artifacts:
  - research/artifacts/defect-coupled-routed-codes-2026-09-12.md
---

Let `U = L_(F_2)(1,2)^x`. `U` has no proper finite-index subgroup, so its profinite topology is
indiscrete and every proper subgroup is non-closed.

**Consequence.** Over the Kun–Thom wreath, deficit witnesses must pass through non-closed stabilizers
of a residually finite actor, and that restricts where a code can save. Over `U` the same condition is
automatic, just as invisibility is (`Rad(U) = U`). So coupling "through a non-closed stabilizer"
carries no filtering content over `U`. What bites there is nonsoficity of the combining window
(`single-maximal-stage-routed-codes-cannot-compress`) and the measure obstructions of the compression
artifact.

Proof: Section 4 of the artifact, route `profinite-localization-vacuous-proof`.
