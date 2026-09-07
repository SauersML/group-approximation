---
rg: 2
id: cyclic-affine-direction-decoder-proof
kind: route
title: Separate the true equality score from independent four-point blocks
target: noisy-affine-direction-decoding-over-cyclic-alphabets
requires: []
artifacts:
  - research/artifacts/unique-games-affine-test-soundness-2026-09-07.md
  - scripts/check_unique_games_affine_soundness.py
  - research/artifacts/unique-games-affine-test-replay-2026-09-07.json
---

Section 3 supplies the full proof, including the concentration inequality.
With `lambda=(1-1/m)rho^2`, the true equality score has mean
`1/m+lambda` and is the average of `N/2` independent `[0,1]`
variables. Each wrong score has mean `1/m` and is the average of
`N/4` independent `[0,1]` variables on cosets of `<b,c>`.

Use threshold `1/m+lambda/2`. The bounded-variable tails and a union
bound yield error at most `(N-1)exp(-N lambda^2/8)`, which is bounded
by the claimed expression because `1-1/m>=1/2`. Weak inequalities in
the bad events cover ties. Equality scores and their fixed tie-breaking
are unchanged by constant shifts, proving invariance and folding of the
coordinate-selector functions.
