---
rg: 2
id: one-hot-selector-parity-barrier-proof
kind: route
title: The affine closure of three one-hot words contains a weight-three word
target: one-hot-selector-parity-barrier
requires: []
artifacts:
  - research/artifacts/compiler-lowering-hyperlinear-2026-08-18.md
---

The solution set of a consistent family of affine `F_2` equations is an affine
subspace, hence is closed under the ternary affine operation

```text
x + y + z.
```

For `m>=3`, the one-hot set contains `e_1,e_2,e_3`, while
`e_1+e_2+e_3` has Hamming weight three and is not one-hot. Therefore the
one-hot set is not affine and cannot be the exact solution set of parity
constraints on the selector bits alone.
