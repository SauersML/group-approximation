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

**Reformulation of the open converse.** The open claim
`stably-finite-simple-rings-have-mf-elementary-groups` of lane `un-architect`, which is the left-to-right
arrow of rung (M) of the root `kazhdan-elementary-approximation-type-mirrors-ring-type`, says exactly that a
countable simple unital ring has an empty middle regime, that is `mf(R) = infinity` or `rig(R) < infinity`.
This theorem shows that simplicity cannot simply be dropped from that statement.

Not claimed: the exact value of `mf(J)` within `{1, 2, 3}`, and anything about soficity of `EL_N(J)`.
