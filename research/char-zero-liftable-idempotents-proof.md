---
rg: 2
id: char-zero-liftable-idempotents-proof
kind: route
title: The lifted trace of a finite-support characteristic-zero lift is a Kaplansky trace and so is positive
target: char-zero-liftable-idempotents-are-never-inverse-defects
requires: [lifted-trace-detects-finite-subgroup-projectives]
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/ternary-anti-central-kernel-normal-forms-2026-09-12.md
---

Section 8.1 of the artifact.
* **Invariance.** In `c_0(G, Z_p)`, idempotent lifts are conjugate by
  `W = E'E + (1-E')(1-E)`, so `T` of any lift computes `t_p`. This is the construction of the
  prerequisite's route.
* **Defects have zero trace.** A pair `ca = 1` lifts to `C0 A0` invertible, and
  `P = A0 (C0 A0)^(-1) C0` gives `T(1 - P) = 0` on a lift of the defect.
* **Positivity.** A finitely generated subfield of `Q_p` embeds in `C`. In `M_n(C*_r(G))` the
  canonical trace is faithful and positive. Blackadar 4.6.2 gives a projection `p` with `xp = p` and
  `px = x`, so `T(x) = T(p) >= 0`, with equality only if `x = 0`.
* **Linear characters.** Section 8.3: the coefficients of `F E` are `|K|/(|H1||H2|)` times roots of
  unity on `H2 H1`, or all zero. They are units, so `f e = f` forces `H2 H1 = H2`.

Trust surface: Blackadar, *K-Theory for Operator Algebras*, Proposition 4.6.2.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 23 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
