---
rg: 2
id: anchored-quantum-parallel-repetition
kind: claim
title: Every two-player anchored game with entangled value below one has exponential parallel-repetition decay
distinct_from:
  anchoring-preserves-nonlocal-game-value: that is the exact affine identity for one anchored copy; this is the quantitative all-coordinate repetition theorem.
  robust-locally-satisfiable-relator-code: that asks for sparse normalized-Hilbert--Schmidt soundness of group relators; this theorem concerns game-winning probability and does not preserve a group ball or compile relators.
artifacts:
  - research/artifacts/three-paper-cairn-ingestion-2026-08-20.md
---

There is a universal constant `c>0` such that if `G_perp` is an
`alpha`-anchored two-player game, its answer alphabets are `A,B`, and

```text
omega*(G_perp) < 1-epsilon,
```

then for every `n>=1`,

```text
omega*(G_perp^n)
  <= (4/epsilon)
     exp(-c alpha^48 epsilon^17 n / s),             (APR1)

s = max(log |A x B|, 1).                            (APR2)
```

The stronger dimension-sensitive form says that whenever

```text
p >= (4/epsilon)
     exp(-c alpha^48 epsilon^17 n / s),
```

the least local Hilbert-space dimension needed to win `G_perp^n` with
probability at least `p` is at least the least dimension needed to win one copy
with probability at least `1-epsilon`.

The theorem is a quantum-game gap amplifier.  It does not by itself amplify a
normalized-HS presentation defect, manufacture a group, or solve Cairn's
`hs-pcp-boone-compiler` hole; those conversions require separate syntax and
soundness-preservation arguments.
