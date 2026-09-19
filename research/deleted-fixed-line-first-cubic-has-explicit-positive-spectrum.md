---
rg: 2
id: deleted-fixed-line-first-cubic-has-explicit-positive-spectrum
kind: claim
title: A determinant-neutral deleted fixed line leaves an explicit rank-two cubic spectrum
distinct_from:
  even-weil-second-cubic-has-a-rank-six-determinant-gap: that uses determinant minus one for the second cubic on p=5 mod 8; this computes the full nontrivial spectrum of the first cubic when the determinant is neutral.
  direct-sum-weil-compressions-have-quadratic-padding: that adds the resulting block energies over a canonical family; this is the abstract one-line compression calculation.
  bs14-flexible-cross-packet-boundary-reconciliation: that asks for a boundary charge for arbitrary mixed packet coefficients; this treats one exact deleted-line chart and its orthogonal sums.
---

Let `H=Cq (+) P H`, let `X=X*=X^(-1)`, and let `U` be a unitary fixing
`q`.  Assume

```text
(XU)^3=1,                 a=<q,Xq> in (0,1).          (DFC1)
```

Put `A=PXP`, `X_0=sgn(A)`, and `U_0=U|_(PH)`.  Then the unitary

```text
W=(X_0 U_0)^3                                               (DFC2)
```

is the identity off a subspace of dimension at most two, and its two
possibly nontrivial eigenvalues are `lambda^3,lambda^(-3)`, where

```text
lambda+lambda^(-1)=-2a/(1+a).                         (DFC3)
```

Consequently

```text
||W-1||_F^2
 =4(1-a)^2(1+2a)/(1+a)^3.                             (DFC4)
```

In particular, the determinant is one but the residual is uniformly
nonzero whenever `a` stays away from one.  Thus determinant neutrality does
not permit the deleted boundary mode to disappear: it appears as a
conjugate pair of spectral-flow angles rather than one parity eigenvalue.

For the even-Weil fixed-line compression at a prime `p=1 mod 8`, take
`U=S^2` and `a=p^(-1/2)`.  Since `p>=17`, `a<1/4`, and `(DFC4)` gives the
convenient universal estimate

```text
||(X_0 S_0^2)^3-1||_F^2 >= 144/125.                   (DFC5)
```

The exact value tends to four as `p` tends to infinity.  This supplies the
positive block charge missing from the determinant argument on the entire
`p=1 mod 8` progression.

