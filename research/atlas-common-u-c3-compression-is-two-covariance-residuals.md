---
rg: 2
id: atlas-common-u-c3-compression-is-two-covariance-residuals
kind: claim
title: The gauge-free common-U C3 compression is exactly two covariance residuals
distinct_from:
  atlas-a4-two-c3-line-carriers-have-exact-angle-gap: that computes the angle gap after the collision line operator has been exposed; this gives an exact sum-of-squares formula for the remaining compression leakage.
  atlas-shifted-factorizations-have-independent-right-gauge: that rules out choosing compatible edge witnesses; this formula contains only the literal common U and no factorization witnesses.
---

Let `a` generate the order-three subgroup `C_6 triangleleft H_6` and put

```text
P=P_6=(1+a+a^2)/3,
C(U)=U^* rho(b_0) U,
Z(U)=E_K^- C(U) E_K^+.
```

Then the last gauge-free leakage in `(A4-C3-9)` has the exact
Pythagorean/sum-of-squares expansion

```text
||Z-PZP||_2^2
 =||(1-P)ZP||_2^2+||Z(1-P)||_2^2
 =1/6 sum_(m=1)^2 ||(a^m-1)ZP||_2^2
   +1/6 sum_(m=1)^2 ||Z(a^m-1)||_2^2.                 (A4-C3-SOS)
```

In particular, exact compression is equivalent to just the two covariance
equations

```text
(a-1)E_K^- C(U)E_K^+P=0,
E_K^- C(U)E_K^+(a-1)=0.                               (A4-C3-COV)
```

This identifies the precise missing joint equation.  None of the fourteen
rank-three packet edges has `b_0` as an endpoint
(`atlas-two-holonomy-endpoint-localization`); every edge controls a conjugate
of one packet endpoint only.  Consequently neither equation in
`(A4-C3-COV)` is a one-edge centralizer consequence.  The collision word is
the only displayed relation containing `C(U)`, while the `H_6` generator `a`
enters only through the other packet component.  Any proof of `(A4-C3-9)`
must therefore produce exactly these left and right covariance residuals by a
joint packet--collision cycle identity (or by a matrix-only trace
obstruction).  A packet-only or collision-only sum of squares cannot contain
the required mixed operator.

The formulation is quantitatively stable without choosing gauges.  If `U,V`
are unitaries, then

```text
||C(U)-C(V)||_2 <= 2||U-V||_2,
||[Z(U)-PZ(U)P]-[Z(V)-PZ(V)P]||_2 <= 4||U-V||_2.
```

Thus the obstacle is not continuity of the canonical readout.  It is the
absence, so far, of a common-`U` identity controlling the two explicit mixed
covariances `(A4-C3-COV)` from the fourteen shifted distances and the
collision residual.
