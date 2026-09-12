---
rg: 2
id: bs14-haar-fixed-source-quantile-proof
kind: route
title: Use Haar spectral quantiles and the inversion source equation
target: bs14-regular-character-forces-sublinear-fixed-source
requires:
  - bs14-character-split-leaves-only-the-regular-microstate-face
  - bs14-trivial-boundary-inversion-forces-r-fixed-source
---

Fourier uniqueness turns `(RFS1)` into weak convergence of the spectral
measures to Haar measure.  Portmanteau applied to the singleton `{1}` gives
`(RFS2)`.

Let `Q_n` project onto `Fix(V_n)`.  Since `V_nQ_n=Q_n`,

```text
||R_n-V_n||_2^2 >= d_n^(-1)||(R_n-1)Q_n||_F^2.       (RFP1)
```

Ky Fan's minimum principle says the right side is at least the sum of the
smallest `rank(Q_n)` eigenvalues of `|R_n-1|^2`, divided by `d_n`.  Under
Haar spectral convergence, the limiting minimizing arc is
`[-pi alpha,pi alpha]`, so the lower bound is

```text
(1/(2pi)) integral_(-pi alpha)^(pi alpha)
                  (2-2 cos theta) d theta
=2 alpha-(2/pi)sin(pi alpha).                         (RFP2)
```

Taylor expansion proves `(RFS4)`.  Finally `(TBI2)` gives `RB=B`, hence
`ran(B) subset Fix(R)` and `(RFS5)` follows from `(RFS2)`.

