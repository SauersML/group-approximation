---
rg: 2
id: paired-frame-moving-kernel-is-a-rank-one-veronese-clock
kind: claim
title: The transported paired-frame kernels have a fixed core and one moving Veronese line
artifacts:
  - experiments/paired_frame_moving_kernel_orbit.py
distinct_from:
  paired-frame-fixed-kernel-polynomial-clock-no-go: that rules out a degree clock inside the stabilizer of one kernel; this moves the kernel and proves the entire nonstationarity is confined to one relative relation coordinate.
  alternating-free-ring-shears-have-strict-degree-drift: that computes degree growth on the original two-dimensional module; this computes its exterior-square orbit on the actual paired-frame relation kernel.
  support-packet-paired-word-frame-exposes-forbidden-rank: that produces one three-dimensional binary edge kernel; this identifies the geometry of all its polynomially transported copies.
---

Let `R=F_2[x]`, let

```text
S=[[1+x^2,x],[x,1]],       T=diag(S,S) in GL_4(R),
K_n=wedge^2(T^n)(K_0) subset wedge^2(R^4),              (MVK1)
```

where `K_0` is the paired-frame relation kernel.  In the wedge basis
`(01,02,03,12,13,23)`,

```text
K_0=span{e_01,e_13,e_23}.                               (MVK2)
```

For every `n`, there is a direct decomposition

```text
K_n = K_fixed direct_sum L_n,
K_fixed=span{e_01,e_23},        dim_R L_n=1.             (MVK3)
```

If the second row of `S^n` is `(c_n,d_n)`, then

```text
L_n=R [c_n^2 e_02 + c_n d_n(e_03+e_12)+d_n^2 e_13].    (MVK4)
```

For `n>=1`, the four nonzero coefficient degrees in `(MVK4)` are

```text
4n-2, 4n-3, 4n-3, 4n-4.                                (MVK5)
```

The lines `L_n` are pairwise distinct over `F_2(x)`.  Consequently, for
`m!=n`,

```text
K_m intersect K_n = K_fixed.                            (MVK6)
```

Thus the moving-kernel atlas is neither a hidden high-rank construction nor
a finite periodic reservoir.  It is exactly a fixed rank-two core plus one
nonreturning relative coordinate, with a strictly increasing leading-degree
label.  All moving lines lie in the three-dimensional symmetric-square
subspace `span{e_02,e_03+e_12,e_13}`.
