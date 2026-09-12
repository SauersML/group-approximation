---
rg: 2
id: affine-shift-games-have-vanishing-value
kind: claim
title: Quadratically shifted affine-pair games have value at most two over the square root of the alphabet size
artifacts:
  - research/artifacts/unique-games-affine-test-soundness-2026-09-07.md
  - scripts/check_unique_games_affine_soundness.py
  - research/artifacts/unique-games-affine-test-replay-2026-09-07.json
---

For every `N=4^r`, `r>=1`, let `F=GF(N)`, left vertices and labels
be `F`, right vertices be `F*`, and the right alphabet at `b` be
`F/<b>`. On the complete bipartite graph, set

```text
pi_(u,b)(a) = [a+u b^2]_b.
```

This is a uniformly weighted biregular 2-to-1 game `G_N`, with every
left vertex seeing every nonzero affine pairing direction exactly once.
Its value is at most `(1+sqrt(1+12N))/(2N) <= 2/sqrt(N)`.
An equal-degree regular cloning preserves its value and pairing distribution.

The statement constructs explicit low-value instances, not an NP-hardness
reduction. Its relevance is the source side of
`affine-long-code-test-has-no-uniform-soundness`.
