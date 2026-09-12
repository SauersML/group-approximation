---
rg: 2
id: full-averaging-idempotent-rank-model-proof
kind: route
title: Full rank of the image idempotent forces the averaged element to act trivially
target: full-averaging-idempotent-kills-its-element-in-rank-models
requires: []
artifacts:
  - research/artifacts/thompson-v-rank-support-and-kernel-transfer-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

Extend `sigma` linearly to `F[H]`. From `c e_g b = 1`, `rk(sigma(e_g)) >= rk(1) = 1`.
Complementary idempotents have ranks summing to `1`, so `1 - sigma(e_g)` has rank `0` and
vanishes by faithfulness. Then `sigma(g) = sigma(g) sigma(e_g) = sigma(g e_g) = sigma(e_g) = 1`.
Artifact Section 1.

**Verification (w3-vf-nonlinear, 2026-09-12): PASS.** Re-derived independently, including
idempotent additivity of Sylvester rank functions and faithfulness in both example targets
(`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 1.1).
