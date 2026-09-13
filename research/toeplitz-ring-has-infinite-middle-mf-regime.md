---
rg: 2
id: toeplitz-ring-has-infinite-middle-mf-regime
kind: claim
title: The Toeplitz-Jacobson algebra is neither eventually MF nor eventually MF-rigid, so the paradox-measure dichotomy needs simplicity
artifacts:
  - research/artifacts/un-open-2-mf-spectrum-2026-09-13.md
---

Let `J = F_2<s,t | ts = 1>` be the Toeplitz-Jacobson algebra and `e = 1 - st != 0`.

**Theorem.** `mf(J) <= 3` and `rig(J) = infinity`, for the MF thresholds of
`mf-rigidity-is-monotone-in-matrix-rank`. Hence for every `N >= 4` the group `EL_N(J)` is neither MF nor
MF-rigid: it is not MF, yet it has a nontrivial MF quotient. The middle regime of `J` contains every
`N >= 4`.

**Reading.** The paradox-measure dichotomy of the UN program is not a dichotomy for arbitrary rings. `J` is
not simple: the ideal `JeJ` is proper, since `J/JeJ = F_2[z, z^(-1)] != 0`, which is exactly the failure of
the fullness hypothesis that lane `un-calibration` isolated as its refutation F4. The theorem quantifies how
badly the dichotomy fails without that hypothesis: the middle regime is infinite.

**Relation to the open converse (corrected by lane `un-m-converse`).** The open claim
`stably-finite-simple-rings-have-mf-elementary-groups`, the left-to-right arrow of rung (M) of the root
`kazhdan-elementary-approximation-type-mirrors-ring-type`, is **not** the statement that simple rings have an empty
middle regime. As `research/artifacts/un-m-converse-simple-spectrum-2026-09-13.md` §1 shows, "empty middle regime",
"`mf(R) = infinity` or `rig(R) < infinity`" and the open claim are three inequivalent statements. The open claim is
equivalent to: every simple stably finite `R` has `rig(R) = infinity` and an empty middle regime.

This theorem shows that the lifting half (empty middle regime) genuinely needs simplicity. `EL_N(J, JeJ)` is a proper
non-central normal subgroup, and the middle regime of `J` is infinite. When `EL_N(R)` is simple modulo a trivial centre,
the middle regime at `N` is empty (`simple-el-group-middle-regime-is-a-central-extension-effect`).

Not claimed: the exact value of `mf(J)` within `{1, 2, 3}`, and anything about soficity of `EL_N(J)`.
