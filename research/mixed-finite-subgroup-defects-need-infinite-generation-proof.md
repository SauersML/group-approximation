---
rg: 2
id: mixed-finite-subgroup-defects-need-infinite-generation-proof
kind: route
title: Separate the difference by the additive lifted trace inside one finite group algebra
target: mixed-finite-subgroup-defects-need-infinite-generation
requires:
  - lifted-trace-detects-finite-subgroup-projectives
artifacts:
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
  - research/artifacts/mixed-finite-subgroup-defects-2026-09-12.md
---

The additive lifted trace `t_p` of `lifted-trace-detects-finite-subgroup-projectives`
is positive on every nonzero idempotent of a single finite group algebra
`M_n(F_p[H])` (LFT1) and vanishes on every Kaplansky defect module (a defect is
`I - AB` with `BA = I`, so its class is `[free] - [free] = 0` in `K_0`). When
`<H_1, H_2>` is finite, `e`, `f` and `e - f` all lie in one such `M_n(F_p[H])`,
so `t_p(e - f) = t_p(e) - t_p(f) > 0`, which a defect cannot have. The full
argument is in the claim body and in Section 1 of the artifact.

*Verification by `w3-vf-linear` (2026-09-12), Section 9.1 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: PASS after one precision repair. The claim allows f = e, where A = B = I is a configuration. The proof needs f != e, that is, a nonzero defect. With that repair it is consequence 2 of lifted-trace-detects-finite-subgroup-projectives at H = <H_1, H_2>.*

*Verification by `w3-vf-linear` (2026-09-12), Section 12.3 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: Update: correct, but the claim's 'only surviving shape' framing is stale. Infinite joins are also excluded, by nested-two-finite-subgroup-idempotents-have-strict-rank.*
