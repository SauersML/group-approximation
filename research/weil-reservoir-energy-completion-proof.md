---
rg: 2
id: weil-reservoir-energy-completion-proof
kind: route
title: Apply the positive fixed-corner identity to the mixed Weil reservoir
target: weil-reservoir-mixing-has-energy-paid-completion
requires:
  - even-weil-fixed-line-compression
  - positive-fixed-corner-cubic-energy-charges-deleted-rank
  - bs14-low-rank-boundary-surgery-preserves-the-regular-face
  - direct-sum-weil-compressions-have-quadratic-padding
---

On the fixed line of the level-`p` even-Weil block, `S^2` is the identity
and the normalized Fourier involution has scalar compression
`p^(-1/2)`.  Therefore on the full deleted reservoir

```text
C=QXQ
```

is positive with spectrum contained in `(0,1/sqrt(5)]`.  Common conjugacy
and arbitrary unitary mixing inside `QH` preserve this spectral statement.

Apply `positive-fixed-corner-cubic-energy-charges-deleted-rank` to the first
cubic with `U=S^2` and `a_0=1/sqrt(5)`.  Its exact identity gives

```text
||(X_0S_P^2)^3-1||_F^2
 >= f(1/sqrt(5)) rank(Q),
f(t)=4(1-t)^2(1+2t)/(1+t)^3.
```

Thus `(WRM2)` holds with `c_0=f(1/sqrt(5))`; adding the nonnegative second
cubic energy only strengthens it.

Restoring `QH` gives back the original exact representation by construction.
The polar-compression estimates in
`bs14-low-rank-boundary-surgery-preserves-the-regular-face` show that every
generator changes by unnormalized Frobenius square `O(k)`.  After padding
and normalizing by `d+k` this proves the first inequality in `(WRM3)`; the
second is `(WRM2)`.  No decomposition of the residual into prime blocks is
used in the estimate.
