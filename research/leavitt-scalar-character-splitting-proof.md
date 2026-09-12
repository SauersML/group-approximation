---
rg: 2
id: leavitt-scalar-character-splitting-proof
kind: route
title: Character orthogonality on the central scalar subgroup
target: leavitt-unit-group-algebras-split-over-scalar-characters
requires: []
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/leavitt-host-survey-scalar-characters-2026-09-12.md
---

Section 1 of the artifact. `F_q^x` is cyclic of order `q - 1`, prime to `p`, and contains every
`(q-1)`-th root of unity. So the characters of the central scalar subgroup form its full dual, and
orthogonality gives central orthogonal idempotents summing to `1`. The evaluation sends `[lambda]` to
`lambda`, so it sends `eps_chi` to the inner product of `chi` with the identity character. The padding
identity `C A' = c a + (1 - eps_chi)` is direct, and so is `sum_lambda lambda^(-1) = 0` for `q > 2`.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 9 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
