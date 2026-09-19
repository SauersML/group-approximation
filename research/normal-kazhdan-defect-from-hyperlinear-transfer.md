---
rg: 2
id: normal-kazhdan-defect-from-hyperlinear-transfer
kind: route
title: Specialize the arbitrary tracial-kill detector to a compression defect
target: normal-kazhdan-defect-non-mf
requires: [hyperlinear-killed-normal-kazhdan-mf-transfer]
artifacts:
  - research/artifacts/hyperlinear-to-mf-saturation-compiler-2026-08-22.md
  - GroupApproximation/Sofic/NormalKazhdanHyperlinearKilled.lean
  - GroupApproximation/Sofic/NormalKazhdanCompressionObstruction.lean
---

## Why sufficient

For a `KazhdanCompressionCore C`, the kernel-checked theorem

```text
KazhdanCompressionCore.defectNormal_hyperlinear_killed
```

proves that every element of `C.defectNormal` vanishes in the normalized-HS
shadow of every operator-norm almost representation.  Apply
`hyperlinear-killed-normal-kazhdan-mf-transfer` with
`D=C.defectNormal`.  Every normal property-`(T)` subgroup `K <= D` lies in
the norm-MF residual, and if `K` is nontrivial no faithful norm-corona
homomorphism can exist.

This factors the concrete theorem through the general hyperlinear-to-MF
bridge and makes clear that compression is a producer of the kill theorem,
not part of the moving-corner detector's interface.
