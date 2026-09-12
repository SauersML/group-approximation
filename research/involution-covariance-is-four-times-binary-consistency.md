---
rg: 2
id: involution-covariance-is-four-times-binary-consistency
kind: claim
title: Involution covariance energy is four times the binary PVM consistency defect
---

Let `S,T` be self-adjoint involutions in a finite matrix algebra with normalized
trace and put

```text
P_S(+)= (1+S)/2,    P_S(-)= (1-S)/2,
P_T(+)= (1+T)/2,    P_T(-)= (1-T)/2.
```

These are binary projective measurements.  With `consDefect` the tracial
matching defect of `consistency-defect-is-state-dependent-distance`, one has
the exact identity

```text
||S-T||_2^2 = 4 consDefect(P_S,P_T).                  (BIN-CONS)
```

Thus every two-generator `S_3` covariance energy

```text
a^2+b^2
```

is exactly four times the sum of the two associated binary readout
consistency defects.  In particular the atlas threshold `1/128` is the binary
agreement threshold `1/512`.
