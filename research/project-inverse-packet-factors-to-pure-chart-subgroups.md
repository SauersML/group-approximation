---
rg: 2
id: project-inverse-packet-factors-to-pure-chart-subgroups
kind: route
title: Project each corrected factor into its residually finite pure chart
target: inverse-packet-conjugator-must-mix-s-and-t-charts
requires:
  - pure-leavitt-chart-linear-groups-are-residually-finite
  - subgroup-supported-one-sided-inverse-rigidity
  - both-rank-three-factors-must-be-packet-corrected
  - conjugated-s3-packets-live-on-n-double-cosets
artifacts:
  - research/artifacts/one-nonnormal-packet-corner-correction-2026-08-21.md
---

If `x` is in the `t`-chart group, the complete corrected left factor,
including `e` and the constant packet, is supported there.  Project its
ambient right inverse into that directly finite group algebra and evaluate.
For `x` in the `s` chart, use `x^-1` and the corrected right factor instead.
The normalizer case is already zero by the fourth prerequisite.
