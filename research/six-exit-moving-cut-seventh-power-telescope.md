---
rg: 2
id: six-exit-moving-cut-seventh-power-telescope
kind: claim
title: Six moving-cut exits control the compressed seventh-power product
distinct_from:
  order-seven-anchor-stops-at-whitehead-compression-leakage: that uses one fixed compression projection and charges six repeated copies of its one-step boundary; this permits six different intermediate moving cuts.
  order-seven-first-exit-is-not-seven-step-leakage: that refutes control from one first-exit operator; this assumes the actual transition exit at every one of the six intermediate stages.
  moving-order-seven-stage-gauges-have-coboundary-drift: that shows the resulting typed product can contain seven different reservoir gauges; this proves only the operator telescope and does not identify those gauges.
---

**ESTABLISHED SIX-EXIT TELESCOPE.**  Let `T` be a contraction on a finite
tracial matrix algebra and let `E_0,...,E_6` be projections.  Put

```text
W=E_0 T E_6 T E_5 T ... T E_1 T E_0.                 (SET1)
```

Then

```text
||W-E_0||_2
 <= ||E_0(T^7-1)E_0||_2
    +sum_(k=0)^5 ||(1-E_(k+1))T E_k||_2.              (SET2)
```

Consequently, if

```text
Xi=sum_(k=0)^5 ||(1-E_(k+1))T E_k||_2^2,             (SET3)
```

then

```text
||W-E_0||_2 <= ||E_0(T^7-1)E_0||_2+sqrt(6 Xi).        (SET4)
```

There is no dependence on the matrix dimension or the ranks of the moving
cuts.

To prove the estimate, set

```text
B_k=T^kE_0,
C_0=E_0,
C_k=E_k T E_(k-1) T ... T E_0       (1<=k<=6).        (SET5)
```

Since `C_k=E_kC_k` and every `C_k` is contractive,

```text
B_(k+1)-C_(k+1)
 =T(B_k-C_k)+(1-E_(k+1))T C_k,
```

and therefore

```text
||B_(k+1)-C_(k+1)||_2
 <=||B_k-C_k||_2+||(1-E_(k+1))T E_k||_2.              (SET6)
```

Iterating `(SET6)` through `k=0,...,5` gives

```text
||T^6E_0-C_6||_2
 <=sum_(k=0)^5||(1-E_(k+1))T E_k||_2.                 (SET7)
```

Now `W=E_0TC_6`; left multiplication by `E_0T` is contractive, so compare
it with `E_0T^7E_0` and then add the seventh-power relator defect.  This is
`(SET2)`.  Cauchy--Schwarz gives `(SET4)`.

Only six transition exits occur because the final range compression `E_0`
is already the leftmost factor in `(SET1)`.  If a construction controls all
seven cyclic transition boundaries as in `(GMC2)`, it supplies these six in
particular.

The lemma completes the analytic telescope in the growing order-seven lane.
It does not prove that the seven compressed transition factors have one
common reservoir involution.  Their typed product can still be
`D_6...D_0`; the cross-stage gauge lock remains separate.
