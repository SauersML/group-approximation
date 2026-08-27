---
rg: 2
id: schur-marked-character-transfer-gap-proof
kind: route
title: Exhaust the mark-preserving packet charts and diagonalize their exact average
target: schur-marked-character-transfer-gap
requires: []
artifacts:
  - experiments/schur_marked_transfer_spectrum.py
  - experiments/schur-marked-transfer-spectrum.json
---

The verifier exhausts all `168` matrices in `GL(3,2)`, retains exactly the ten
involutions fixing `J` and admitting a nonzero packet pivot, and constructs
their contragredient permutation matrices on the `J=-1` character slice using
rational arithmetic.  Entrywise counting gives the displayed matrix.

For a zero-sum vector `v`,

```text
(Tv)_i=(2/5)v_i+(1/5)sum_(j!=i)v_j=(1/5)v_i.
```

The constant vector is fixed because the matrix is bistochastic.  These two
identities give the complete spectrum and singular spectrum without numerical
approximation.  The script asserts every count and matrix entry before
emitting the committed certificate.
