---
rg: 2
id: scalar-two-root-rank-data-calibration-proof
kind: route
title: Check the Boolean function against conjugation invariance and root subadditivity
target: scalar-two-root-rank-data-cannot-force-the-identity
requires: []
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/el3-compressor-root-pair-calculus-2026-09-12.md
---

Artifact Section 2.
* `delta` is conjugation invariant because rank is invariant under conjugation by units of `M`.
* **Subadditivity.** Root subgroups are abelian and `n^2 = 0`, so
  `n_12(a+a') = X + X' + XX'` with `X`, `X'` commuting. Hence
  `Y n_12(a+a') = YX(1+X') + YX'`, and similarly in `b`.
* **Lemma 4.** Unit moves preserve unit pairs, and both compressor moves need a non-unit input and
  produce non-unit outputs.
* **Proposition 5.** `eps [a != 0][b != 0]` passes all three conditions, since conjugation preserves
  nontriviality of root elements.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 49 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
