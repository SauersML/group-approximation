---
rg: 2
id: weighted-pinching-channel-transfer-proof
kind: route
title: Sign weighted reflection averages and compare channels by operator Cauchy--Schwarz
target: row-square-equality-variance-transfers-averaged-pinching-gap
requires:
  - common-cut-contraction-sign-has-complete-balanced-energy-ledger
  - averaged-pinching-channels-are-row-square-lipschitz
---

Expanding the weighted square in `(REV2)` and using
`sum_u lambda_(u|i)Q_u=S_i` proves `V_i=I-S_i^2` without any commutativity.
Since `R_i` is a spectral function of `S_i`,

```text
 sum_(u:i(u)=i)lambda_(u|i)(Q_u-R_i)^2
   =2(I-|S_i|)<=2(I-S_i^2)=2V_i.                      (WPT1)
```

Thus, for `D_u=Q_u-R_(i(u))`, `(REV3)` implies

```text
 sum_u w_uD_u^2<=2epsilon I.                           (WPT2)
```

Repeat each shared sign `R_i` with its occurrence weight.  The weighted
row-square hypothesis `(WPT2)` is exactly the input of
`averaged-pinching-channels-are-row-square-lipschitz`, which gives `(REV5)`.
This is where arbitrary unequal occurrence weights are absorbed; no
individual displacement estimate is used.

Now `||H_Q-H_R||<=kappa`.  The min--max principle for finite-dimensional
selfadjoint operators places every eigenvalue of `H_R` within `kappa` of
the corresponding eigenvalue of `H_Q`, proving `(REV6)` and the Green bound.
No part of this argument uses equal conditional weights or a lower bound on
`mu_i`.

For sharpness, represent traceless selfadjoint `2 by 2` matrices by Bloch
vectors.  Pinching by a reflection is orthogonal projection onto its axis.
Axes at angle `theta` give projection distance `sin(theta)`, while direct
Pauli multiplication gives `(Q-R)^2=4sin^2(theta/2)I`.
