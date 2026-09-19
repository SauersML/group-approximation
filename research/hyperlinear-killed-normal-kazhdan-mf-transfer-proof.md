---
rg: 2
id: hyperlinear-killed-normal-kazhdan-mf-transfer-proof
kind: route
title: Extract and self-normalize the ambient Kazhdan moving corner
target: hyperlinear-killed-normal-kazhdan-mf-transfer
requires: []
artifacts:
  - research/artifacts/hyperlinear-to-mf-saturation-compiler-2026-08-22.md
  - GroupApproximation/Sofic/NormalKazhdanHyperlinearKilled.lean
  - GroupApproximation/Sofic/InternalRadicalGap.lean
---

## Why sufficient

This is machine-checked as

```text
KazhdanCompressionCore.normalKazhdan_le_normMFResidual_of_hyperlinear_killed
KazhdanCompressionCore.normalKazhdanPart_le_normMFResidual_of_hyperlinear_killed
KazhdanCompressionCore.not_isWeakMF_of_normalKazhdan_le_hyperlinear_killed
KazhdanCompressionCore.normalKazhdan_le_normMatrixCStarCoronaKernel_of_hyperlinear_killed.
```

Despite the namespace, none of these declarations assumes a compression
core.  They consume an arbitrary subgroup `D` and the explicit quantified
op-to-HS kill hypothesis.

Suppose a norm-corona representation keeps an element of `K` alive.  Pass to
the countable image, where the image of `K` remains normal, Kazhdan, and
nontrivial.  `InternalRadicalGap.exists_setup` produces its Kazhdan gap, and
`exists_ambientMovingCornerSchedule` produces moving projections that are
asymptotically invariant under the ambient image because `K` is normal.
Compression and polar correction give an ambient operator-norm almost
representation on those corners.  Normalizing by their own ranks forces a
fixed Kazhdan generator to survive in normalized HS norm.  Pulling back to
`E` contradicts the kill hypothesis on `D` because `K <= D`.

The `normalKazhdanPart` conclusion follows by taking the supremum of all such
normal Kazhdan subgroups and using that the MF residual is a subgroup.
