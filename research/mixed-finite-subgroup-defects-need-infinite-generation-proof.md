---
rg: 2
id: mixed-finite-subgroup-defects-need-infinite-generation-proof
kind: route
target: mixed-finite-subgroup-defects-need-infinite-generation
requires:
  - lifted-trace-detects-finite-subgroup-projectives
artifacts:
  - research/artifacts/mixed-finite-subgroup-defects-2026-09-12.md
---

The additive lifted trace `t_p` of `lifted-trace-detects-finite-subgroup-projectives`
is positive on every nonzero idempotent of a single finite group algebra
`M_n(F_p[H])` (LFT1) and vanishes on every Kaplansky defect module (a defect is
`I - AB` with `BA = I`, so its class is `[free] - [free] = 0` in `K_0`). When
`<H_1, H_2>` is finite, `e`, `f` and `e - f` all lie in one such `M_n(F_p[H])`,
so `t_p(e - f) = t_p(e) - t_p(f) > 0`, which a defect cannot have. The full
argument is in the claim body and in Section 1 of the artifact.
