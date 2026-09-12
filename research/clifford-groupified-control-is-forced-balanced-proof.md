---
rg: 2
id: clifford-groupified-control-is-forced-balanced-proof
kind: route
title: Conjugate the two control spectral projections by its Pauli partner
target: clifford-groupified-control-is-forced-balanced
requires:
  - finite-schur-clifford-packet-flexible-hs-exactification
---

The central projection `Q` commutes with `x,z`. On its range `J=-I`, hence
`[x,z]=J` is the anticommutation identity `xz=-zx`. Therefore

```text
x Q(I-z)x/2=Q(I+z)/2.
```

Trace invariance under unitary conjugation makes the two traces equal. Their
sum is `tau(Q)`, proving `(CGB1)`. For `(CGB2)`, either telescope the bounded
degree projection/conjugacy polynomial directly after spectral rounding, or
exactify the fixed finite Pauli subgroup and transfer the projection traces.
