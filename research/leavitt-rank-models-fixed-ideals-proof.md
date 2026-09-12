---
rg: 2
id: leavitt-rank-models-fixed-ideals-proof
kind: route
title: Apply fixed-ideal conservation to the nine-leaf pair and use simplicity of the unit group
target: leavitt-rank-models-kazhdan-fixed-ideals-are-global
requires:
  - rank-ultraproduct-compressors-conserve-fixed-right-ideals
  - leavitt-unit-group-carries-nontrivial-rigid-defect
  - leavitt-packet-linear-sofic-kills-kaplansky-target
  - binary-leavitt-unit-group-is-simple
artifacts:
  - research/artifacts/rank-row-compression-audit-2026-09-12.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

## Why sufficient

* **Compressors generate.** `leavitt-unit-group-carries-nontrivial-rigid-defect` gives
  that the compressors `u`, `v` and `Gamma` lie in the compression semigroup of
  `Gamma = EL_alpha(R)` and generate `G_L = EL_D(R)`.
* **The whole group.** `leavitt-packet-linear-sofic-kills-kaplansky-target` gives
  `G_L = R^x`.
* **Normal closure.** `binary-leavitt-unit-group-is-simple` and `Gamma != 1` give
  `<<Gamma>>_(R^x) = R^x`.
* **Conclusion.** `rank-ultraproduct-compressors-conserve-fixed-right-ideals`, with
  `G = R^x`, gives
  `Fix^(a,b)(sigma(Gamma)) = Fix^(a,b)(sigma(<<Gamma>>)) = Fix^(a,b)(sigma(R^x))`.

Independently re-derived 2026-09-12 by gk-verify-pos: PASS (Section 19 of the
verification artifact).
