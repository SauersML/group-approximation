---
rg: 2
id: diagonal-links-cat1-from-turning-face-conditions
kind: route
title: Diagonal links of NCP_n are CAT(1) if no chain satisfies the turning-face conditions with its dual
target: noncrossing-partition-diagonal-links-are-cat1
requires:
  - no-noncrossing-chain-satisfies-turning-face-conditions
artifacts:
  - research/artifacts/zp-braid-cat0-turning-face-reduction-2026-09-13.md
---

Induction on `n`. The base cases `n = 3, 4` are graphs of girth at least `2π` (HKS Remark 4.1). For `n >= 5`, apply
Theorem R of the artifact: `X_m` is CAT(1) for `m < n` by induction, and the required claim excludes the turning faces
of any unshrinkable short loop in `X_n`, so `X_n` is CAT(1).

Theorem R combines HKS Lemmas 3.7, 3.12, 3.13, 4.8, 4.9, 4.15, the proof of HKS Theorem 4.17 and Bowditch's theorems
(HKS 2.32, 2.33), with two lemmas proved in the artifact: Lemma A (HKS Lemma 4.15 for faces) and Lemma D (the Kreweras
complement is orthogonality for `<y, z> = sum_k (y_1 + ... + y_k) z_k`, so it extends to an isometry of the building).
Unreviewed.
