---
rg: 2
id: two-raw-unweighted-covariance-kills-jacobson-head
kind: claim
title: Direct two-root covariance relations kill the marked Jacobson head
distinct_from:
  two-raw-roots-have-a-uniform-full-carrier-gap: that proves two covariance tests would give the needed spectral gap; this proves why the intended head representation cannot satisfy those tests unweighted
  long-router-square-energy-cannot-control-endpoint-frame: that rules out recovering covariance along a growing path; this rules out adding the missing covariance as a bounded exact relation
  binary-jacobson-head-root-has-opnorm-square-decoder: that asks for a representation-dependent selected occurrence; this proves why an unselected global occurrence cannot work
---

Let

```text
J=F_2<S,T | TS=1>,             Q=1-ST,
h=x_12(Q) in EL_n(J),          n>=4.
```

The one-sided identities are

```text
QS=0,        TQ=0,        QTS=Q,        TSQ=Q,          (TRC1)

QT !=0,      SQ !=0.                                   (TRC2)
```

Accordingly the right-`S` covariance relation is already true:

```text
[h,x_23(S)]=x_13(QS)=1.                                (TRC3)
```

The parallel right-`T` relation is incompatible with the marked head:

```text
[h,x_23(T)]=x_13(QT) !=1.                              (TRC4)
```

More strongly, adjoining `[h,x_23(T)]=1` to the elementary presentation
forces `h=1`. Indeed the new relation kills `x_13(QT)`, and the existing
return with `x_34(S)` then kills

```text
[x_13(QT),x_34(S)]=x_14(QTS)=x_14(Q).                  (TRC5)
```

Constant Weyl conjugacy carries `x_14(Q)` back to `h`.

The left-handed packet has the same obstruction with the orientations
reversed: `TQ=0` is harmless, while forcing the `SQ` descendant to vanish
and returning by `T` kills `Q` through `TSQ=Q`.

In the canonical left regular representation, the proposed dangerous
covariance relator in `(TRC4)` has normalized Hilbert--Schmidt defect
exactly `sqrt(2)`. Thus the intended infinite marked Jacobson
representation does not even approximately satisfy the direct packet.

Consequently `two-raw-roots-have-a-uniform-full-carrier-gap` cannot be
consumed by adding unweighted commutator relations for the head occurrence.
A viable substitute must be head-localized and rectangular: keep the
harmless right-`S` and left-`T` annihilations on different coefficient
occurrences, and charge rather than erase the nonzero descendants `QT` and
`SQ`. Identifying those two one-sided occurrences as one global
intertwiner recreates `(TRC5)` and kills the payload.

DERIVATION
steinberg-return-turns-dangerous-covariance-into-head-proof
