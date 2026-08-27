---
rg: 2
id: positive-fixed-corner-cubic-energy-charges-deleted-rank
kind: claim
title: A positive fixed corner turns cubic Frobenius energy into a block-free rank charge
distinct_from:
  deleted-fixed-line-first-cubic-has-explicit-positive-spectrum: that computes one deleted line; this diagonalizes an arbitrary finite-rank corner and requires no pre-existing packet block decomposition.
  direct-sum-weil-compressions-have-quadratic-padding: that adds already separated Weil blocks; this permits the ambient involution to mix all deleted directions.
  bs14-flexible-cross-packet-boundary-reconciliation: that must reconstruct a suitable boundary corner from an arbitrary near-solution; this proves the energy inequality once such a corner exists.
---

Let `Q` be a finite-rank projection, `P=1-Q`, and let
`X=X*=X^(-1)`.  Let `U` be unitary, fix `QH` pointwise, and satisfy

```text
(XU)^3=1.                                             (PFC1)
```

Assume the corner compression

```text
C=QXQ
```

is positive and has spectrum in `(0,a_0]` for some `a_0<1`.  Put
`A=PXP`, `X_0=sgn(A)`, and `U_0=U|_(PH)`.  Then

```text
||(X_0U_0)^3-1||_F^2
 =Tr_Q f(C),
f(t)=4(1-t)^2(1+2t)/(1+t)^3.                          (PFC2)
```

In particular, `f` is decreasing on `(0,1)`, and hence

```text
||(X_0U_0)^3-1||_F^2 >= f(a_0) rank(Q).               (PFC3)
```

Moreover the residual has rank at most `2 rank(Q)`.  This is a
block-free positive index: determinant phases may cancel and `X` may mix all
deleted directions, but the cubic Frobenius squares cannot cancel.  The
only decomposition used is the intrinsic spectral decomposition of `QXQ`.

For a heterogeneous direct sum of even-Weil fixed lines, `U=S^2` fixes the
whole deleted reservoir pointwise and the standard Fourier normalization
has positive `QXQ`.  If its eigenvalues are bounded by `a_0<1`, `(PFC3)`
charges the entire missing rank even after arbitrary mixing inside that
reservoir.  What this theorem does **not** do is manufacture `Q` from a
given approximate tuple on `PH`; that reverse dilation/authentication step
is the surviving content of
`bs14-flexible-cross-packet-boundary-reconciliation`.

