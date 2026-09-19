---
rg: 2
id: native-weyl-return-s3-proof
kind: route
title: Compute the native two-root Weyl braid and its three-reflection gauge quotient
target: native-weyl-return-gauges-have-s3-model
requires:
  - partial-whitehead-fold-return-has-finite-s6-model
  - one-singer-square-does-not-identify-external-return-gauge
---

On the span of coordinates `7,8`, write

```text
n=[[1,1],[0,1]],              m=[[1,0],[1,1]].         (1)
```

Over `F_2`, both square to one and

```text
nmn=[[0,1],[1,0]]=w.                                  (2)
```

Multiplying `(2)` by `n` and `w` gives `wnw^(-1)=m`, proving the literal
EL20 rows `(NWR1)--(NWR2)`.

For the reservoir calculation, the factorization `w=nmn` gives `D=EFE`.
The conjugacy row gives `F=DED^(-1)`.  Put

```text
D=(1 2),       E=(2 3),       F=(1 3).
```

Conjugation by a transposition simply transports the two points of the
other transposition, so `EFE=(1 2)=D` and `DED=(1 3)=F`.  Meanwhile
`DE=(1 2)(2 3)` is a three-cycle.  Thus all native rows are exact but the
two reservoir factors do not cancel.

For the extension across further root-position squares, assign the target
of every conjugated occurrence to be its literal conjugate.  Both paths
around each mixed square are then the same product in `S_3`.  This proves
the claimed finite extension without any approximation or external input.

