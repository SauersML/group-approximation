---
rg: 2
id: two-cubic-residual-carriers-recover-the-deleted-source
kind: claim
title: Two transverse cubic residual carriers recover the deleted source image
distinct_from:
  positive-fixed-corner-cubic-energy-charges-deleted-rank: that charges the rank but leaves the source direction mixed with one exit direction; this identifies the source as an intersection of two carriers.
  bs14-flexible-cross-packet-boundary-reconciliation: that starts without an exact dilation or a carrier-angle hypothesis; this proves the reverse decoder inside the positive-corner model.
  common-corner-mutual-bicommutant-extraction: that localizes an algebra factor using two packet commutants; this is a finite-dimensional spectral-support intersection for two cubic words.
---

Use the setup of
`positive-fixed-corner-cubic-energy-charges-deleted-rank`, but let `U_1,U_2`
both fix `QH` pointwise and satisfy `(XU_i)^3=1`.  Use the same polar
compression `X_0=sgn(PXP)` and put

```text
W_i=(X_0(U_i|_(PH)))^3,
Z_i=ran(W_i-1),
V=P X QH.                                               (TCR1)
```

If `C=QXQ` is positive with spectrum in `(0,1)`, then

```text
Z_i=span(QH,XQH,(XU_i)^2QH) intersect PH,             (TCR2)
dim Z_i=2 rank(Q),
V subset Z_1 intersect Z_2.                            (TCR3)
```

Consequently, under the single transversality condition

```text
Z_1 intersect Z_2=V,                                  (TCR4)
```

the two compressed cubic residuals recover the deleted source image
canonically:

```text
V=ran(W_1-1) intersect ran(W_2-1).                    (TCR5)
```

This decoder is block-free and is unchanged by off-diagonal mixing of the
deleted directions.  Quantitatively, if the second principal cosine between
`Z_1` and `Z_2` is at most `1-gamma`, then the eigenvalue-one spectral
subspace of

```text
P_(Z_1) P_(Z_2) P_(Z_1)
```

is `V`, separated from the remaining spectrum by at least
`1-(1-gamma)^2`.  Standard finite-dimensional spectral perturbation then
makes the decoder Lipschitz with loss depending only on `gamma`.

One cubic alone cannot perform this authentication.  Its residual carrier
has dimension `2 rank(Q)` and contains both the source image `V` and one
exit direction of the same dimension.  The positive energy identity charges
their combined carrier but does not distinguish the two halves.  Thus the
second cubic and a uniform cross-carrier angle are genuinely necessary for
the reverse boundary reconstruction.

