---
rg: 2
id: ir-survival-is-one-compressed-adjoint-moment
kind: claim
title: IR survival is exactly one compressed adjoint mixed moment
distinct_from:
  leavitt-positive-rank-intertwiner-retention: that asks simultaneously for IR1, IR2 and survival; this identifies the minimal scalar survival datum once the same almost-reducing, almost-K-trivial sector has been supplied.
  leavitt-presentation-double-has-all-fold-mf-moments: that prescribes the ordinary group trace of the cross word; this identifies the different adjoint-operator trace which IR3 actually measures.
  diagonal-retention-fusion-coefficient: that characterizes retention of an entire GNS summand by positive-functional domination; this is a finite-coordinate identity for one almost-reducing compression and one quotient element.
---

**ESTABLISHED MINIMAL MIXED MOMENT.** In the notation of
`leavitt-positive-rank-intertwiner-retention`, suppose `P_n` has rank `r_n`
and satisfies `(IR1)--(IR2)`.  Define the compressed adjoint coefficient

```text
c_n(f_0)=r_n^(-1) Tr_(HS)(P_n Pi_n(f_0) P_n).           (CAM1)
```

Then the survival condition `(IR3)` is exactly

```text
liminf_n (2-2 Re c_n(f_0))>0.                           (CAM2)
```

Indeed,

```text
r_n^(-1)||(Pi_n(f_0)-1)P_n||_(HS)^2
 =2-2 Re c_n(f_0).                                     (CAM3)
```

Thus, after `(IR1)--(IR2)`, the one additional scalar condition

```text
limsup Re c_n(f_0)<1                                   (CAM4)
```

is necessary and sufficient for IR retention and hence, through
`leavitt-presentation-double-retention-proves-hyperlinear`, for the proposed
Leavitt hyperlinearity route.

This coefficient is not the ordinary fold moment.  Under the left-right
representation, the latter is the single distinguished-vector coefficient

```text
tr_d(u_n(f_0)v_n(f_0)^*)
 =<Pi_n(f_0)1,1>_(HS)/d_n,                              (CAM5)
```

whereas `(CAM1)` averages `Pi_n(f_0)` over the entire retained sector.
`leavitt-presentation-double-has-all-fold-mf-moments` shows `(CAM5)` can be
assigned any value in `[0,1]` with canonical vertex marginals, without
producing the sector in `(CAM1)`.  Thus the exact scalar formulation of the
remaining IR survival condition is `(CAM1)` on the same sector which pays
`(IR1)--(IR2)`; the uncompressed one-word trace is a different coefficient
and the construction supplies no implication from it to `(CAM1)`.

DERIVATION
compressed-adjoint-moment-identity-proof
