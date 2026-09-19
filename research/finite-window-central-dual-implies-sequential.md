---
rg: 2
id: finite-window-central-dual-implies-sequential
kind: route
title: Apply the finite separator inequality along a canonical HNN microstate sequence
target: sl3-hnn-central-dual-gap-vanishes
requires:
  - sl3-hnn-finite-window-central-dual-gap
---

Let `(phi_n,B_n)` satisfy `(LCG1)--(LCG2)`, and let `M` bound all
`||B_(n,s)||_op`.  Given `epsilon>0`, choose `W,delta` from `(FDG1)--(FDG3)`.
Canonicality gives

```text
max_(w in W)|tr(phi_n(w))| -> 0,
```

presentation defect tends to zero, and `(LCG2)` gives the last inequality
of `(FDG2)`.  Hence `(FDG3)` applies for all sufficiently large `n`, so the
limsup separation gap is at most `epsilon`.  Letting `epsilon` tend to zero
proves `(LCG3)`.
