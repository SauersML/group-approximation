---
rg: 2
id: anchoring-preserves-nonlocal-game-value
kind: claim
title: Independent question anchoring transforms classical and entangled game values by one exact affine formula
distinct_from:
  anchored-quantum-parallel-repetition: that bounds the value of repeated anchored games; this is the exact one-copy value identity and uses no repetition theorem.
artifacts:
  - research/artifacts/three-paper-cairn-ingestion-2026-08-20.md
---

Let `G` be a finite two-player nonlocal game and let `G_perp` be its
`alpha`-anchored version: independently for each player, replace the sampled
question by an anchor symbol with probability `alpha`, and accept
automatically if either question was replaced.  For `0 < alpha < 1`,

```text
omega*(G_perp)
  = 1 - (1-alpha)^2 (1-omega*(G)).                 (AV1)
```

The identical equation holds for the classical value.  In particular,

```text
omega*(G_perp)=1  iff  omega*(G)=1,                (AV2)
omega(G_perp)=1   iff  omega(G)=1.                 (AV3)
```

This is a literal score decomposition: the verifier reaches the original game
with probability `(1-alpha)^2` and accepts automatically otherwise.  A strategy
for either game restricts to the original question set, while any original
strategy extends arbitrarily on the anchor question, so taking suprema preserves
the affine equality.
