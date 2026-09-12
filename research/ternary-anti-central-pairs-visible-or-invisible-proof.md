---
rg: 2
id: ternary-anti-central-pairs-visible-or-invisible-proof
kind: route
title: Transport the field-independent orbit theorem to the anti-central summand and replace augmentation by trace
target: ternary-anti-central-pairs-visible-or-invisible
requires: [ternary-leavitt-swap-problem-splits-at-central-involution]
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/ternary-anti-central-kernel-normal-forms-2026-09-12.md
  - research/artifacts/leavitt-inverse-defect-normal-forms-2026-09-12.md
---

Sections 2 and 3 of the artifact.
* The prerequisite supplies the central idempotents `eps_+-`, and that `pi` factors through
  `S_-` with `pi(eps_-) = 1`.
* Lemma 1, Lemma 2 and Theorem 3 of the binary normal-forms artifact hold over `F_3`, dividing
  by the nonzero coefficient `c_(alpha*)` in Lemma 1.
* Translation by `[w]` or `[r]` preserves `c a = eps_-` and conjugates `ac`.
* Visibility: `1 = pi(p) y pi(p)` forces `pi(p) = 1`.
* The normalizing unit over `t0` is `v = 1 + s0 gamma t1`, with inverse `1 - s0 gamma t1`.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 8 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
