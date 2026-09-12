---
rg: 2
id: finite-support-triangular-two-piece-lifts-refutation-proof
kind: route
title: A vanishing off-diagonal piece is a group shift of a finite-subgroup idempotent ideal, which must be an equality, which evaluation refutes
target: finite-support-triangular-two-piece-s0-lifts-do-not-exist
requires:
  - finite-subgroup-idempotent-ideals-admit-no-proper-group-shift
  - two-piece-s0-lifts-telescope-to-a-corner
artifacts:
  - research/artifacts/triangular-lift-hnn-transfer-2026-09-12.md
---

Artifact Sections 0 and 3.
- **`X = 0`.** It means `[h](1 - E^)A ⊆ (1 - E^)A`, so by the shift theorem `f(1 - E^) = 1 - E^` for
  `f = [h](1 - E^)[h^(-1)]`. Evaluation gives `q P_1 = P_1` with `q = pi(h) P_1 pi(h)^(-1) < P_1`. Contradiction.
- **`Y = 0`.** It means `[h^(-1)]E^A ⊆ E^A`, so `f' E^ = E^` for `f' = [h^(-1)]E^[h]`. Evaluation gives
  `pi(f') P_0 = P_0`, while `pi(f') = pi(h)^(-1) P_0 pi(h)` is strictly below `P_0`. Contradiction.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 17.2 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. The strict containments were re-derived from the cylinder data: `h(1) = g_1^-1(01)` is a proper subset of `1`, and `h^-1(0) = g_2^-1(00)` is a proper subset of `0`.*
