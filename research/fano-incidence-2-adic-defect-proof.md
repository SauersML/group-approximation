---
rg: 2
id: fano-incidence-2-adic-defect-proof
kind: route
title: Square the incidence matrix and reduce its rows modulo two
target: fano-point-line-intertwiner-has-a-2-adic-defect
requires:
  - fano-points-and-lines-have-the-same-complex-permutation-type
---

Every Fano line has three points and every two different lines meet once,
which gives `NN^T=2I+J`.  Its determinant is `9*2^6`, proving the absolute
determinant of `N` is 24.  Over `F_2`, the seven line indicators are the
nonzero functions in the affine four-dimensional space spanned by `1` and
the three coordinate functions.  Those four functions are independent on
`F_2^3 minus {0}`, so the mod-two rank is four.

