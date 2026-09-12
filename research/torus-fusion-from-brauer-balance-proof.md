---
rg: 2
id: torus-fusion-from-brauer-balance-proof
kind: route
title: Compute the Brauer difference of the half-corner projectives and apply the balance theorem at a torus element
target: chart-comparison-must-fuse-torus-classes
requires:
  - split-comparisons-balance-induced-brauer-characters
artifacts:
  - research/artifacts/kaplansky-torus-fusion-brauer-balance-2026-09-11.md
---

Sections 2 and 3 of the artifact.

1. The half-corner artifact gives `f_+ E ~= P E` inside `F_2[K]`, so the
   unreduced and reduced pairs have the same Brauer difference. It also gives
   `f_0 ~ P(1)+St` and `P_0 ~ P(V)+P(V^(2))` over the nontrivial central block
   `F_4[A_5]`. Both pairs have equal chart rank, 40 respectively 32.
2. The modular projective characters of `A_5` are read off the decomposition
   matrix. The difference is `(0, 3, 0, 0)` on the classes `1`, `(123)`, `5A`,
   `5B`.
3. Restriction of scalars from `F_4` to `F_2` multiplies the value at `a z^k` by
   `w^k + w^(2k)`, which is `2` for `k=0` and `-1` otherwise. Weighted by
   centralizer order `9`, the difference is `+2/3` on `T0` and `-1/3` on `T1` and
   on `T2`.
4. Apply the balance theorem at `x in pi(T0)`. The sum
   `2/3 - (1/3)[T1 ~ T0] - (1/3)[T2 ~ T0]` vanishes only if both classes fuse.
