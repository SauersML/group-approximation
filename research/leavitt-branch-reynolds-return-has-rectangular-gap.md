---
rg: 2
id: leavitt-branch-reynolds-return-has-rectangular-gap
kind: claim
title: The canonical branch Reynolds return has the exact rectangular leakage gap
distinct_from:
  target-saturated-reynolds-return-does-not-lock-leavitt-reservoir: that treats an arbitrary contraction between the two Reynolds ranges and separates the two saturation directions; this names the native first-branch formula and computes its leakage from the two child packets.
  leavitt-forward-morita-polar-misses-reynolds-return: that audits the forward left-right coefficient chart on label algebras; this uses its branch transporter contravariantly on the packet commutants and identifies the precise second-child leakage row.
  first-leavitt-weyl-cell-has-exact-rectangular-model: that gives the source and two-child Weyl matrices and branch transports; this computes the corresponding adjoint Gram and proves that all existing marginal/crossed packet relations leave a fixed gap.
---

**ESTABLISHED.**  On a fixed nontrivial order-`p` phase, let `Q_s` be the
source Heisenberg packet and `Q_0,Q_1` the two commuting child packets in the
first affine-Leavitt cell.  Let

```text
R_s,R_0,R_1
```

be their adjoint Reynolds projections.  The two child adjoint actions
commute, so

```text
R_t=R_0R_1=R_1R_0                                      (BRG1)
```

is the Reynolds projection of the full two-child packet.  Let `U_0` be the
first branch transporter and put `V=Ad(U_0)`.  Exact branch covariance gives

```text
V R_s V^*=R_0.                                         (BRG2)
```

The natural cross-typed return operator is therefore

```text
X_0=R_1 V R_s=R_t V R_s.                               (BRG3)
```

The second equality follows from `V R_s=R_0 V R_s` and `(BRG1)`.  Thus
`X_0` first transports the complete source commutant to the first-child
commutant and then asks which part also lies in the transverse child
commutant.

Its Gram trace and leakage are exact:

```text
tr_ad(X_0^*X_0)=tr_ad(R_t)=p^(-4),                     (BRG4)

||(I-R_1)V R_s||_(HS,ad)^2
 =tr_ad(R_s)-tr_ad(X_0^*X_0)
 =p^(-2)-p^(-4).                                       (BRG5)
```

Indeed cyclicity, `(BRG1)`, and `(BRG2)` give

```text
tr_ad(X_0^*X_0)
 =tr_ad(R_1 V R_s V^* R_1)
 =tr_ad(R_1R_0R_1)=tr_ad(R_t).
```

The packet superrank formulas give the last values in `(BRG4)--(BRG5)`.

This calculation holds in the exact rectangular model of
`first-leavitt-weyl-cell-has-exact-rectangular-model`, where `U_0=1`, the
source packet is the first Weyl factor, and `R_1` is conditional expectation
over the transverse Weyl factor.  Hence every currently named relation used
in `(BRG1)--(BRG2)` is exact while the source leakage has the fixed value
`p^(-2)-p^(-4)`.  In particular the child packets' group commutation does
not imply that the **commutant** of one child is fixed by the other child.

There is also a robust one-line reduction.  After exactifying the finite
packets, suppose the branch covariance superoperator error is

```text
a=||V R_s V^*-R_0||_(HS,ad).
```

Then

```text
||(I-R_1)V R_s||_(HS,ad)^2
 >=p^(-2)-p^(-4)-a.                                   (BRG6)
```

This follows by replacing `V R_sV^*` by `R_0` in the trace defining
`X_0^*X_0` and applying Cauchy--Schwarz.  Approximate packet exactification
adds only its fixed finite-group `o(1)` error.

Thus `(BRG3)` is the sharp concrete candidate beneath
`affine-leavitt-source-saturated-reynolds-checksum`, but the current relations
force only target saturation `(BRG4)`.  To close the route one new
finite-matrix return estimate must charge

```text
||(I-R_1)V R_s||_(HS,ad)^2                             (BRG7)
```

to named full-presentation word defects.  Crossed-zero coefficient products,
separate branch covariance, and child packet commutation cannot do so: the
rectangular model makes all of them exact while retaining `(BRG5)`.
