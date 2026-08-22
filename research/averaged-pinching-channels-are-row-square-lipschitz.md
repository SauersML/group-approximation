---
rg: 2
id: averaged-pinching-channels-are-row-square-lipschitz
kind: claim
title: Averaged pinching channels are Lipschitz in operator row-square displacement
distinct_from:
  parity-exact-shared-contractions-have-intrinsic-cp-gap: that assumes literal sharing; this proves stability of the normalized channel under row-square-small occurrence replacement.
  covariant-square-function-has-common-reducing-threshold: that constructs a common low square-function block; this supplies the perturbation estimate used on that block.
  repeated-ldpc-shared-face-marginal-synchronization: that asks for literal equality; this transfers a finite-time CP gap without first obtaining literal equality.
---

ESTABLISHED.  Let `(w_r)` be nonnegative weights summing to one, let
`Q_r,S_r` be selfadjoint contractions, put `D_r=Q_r-S_r` and

```text
 H=sum_r w_r D_r^2,
 A_Q(T)=sum_r w_r(T+Q_rTQ_r)/2,
 A_S(T)=sum_r w_r(T+S_rTS_r)/2.                         (APLIP1)
```

Then, at every matrix amplification,

```text
 ||A_Q-A_S||_(2->2)<=sqrt(||H||_infinity).              (APLIP2)
```

If both channels are `L_2` contractions, telescoping gives

```text
 ||A_Q^K-A_S^K||_(2->2)<=K sqrt(||H||_infinity).        (APLIP3)
```

Consequently, if `A_S^K` contracts off a fixed-point expectation `E` by
`rho_K`, then

```text
 ||(I-E)A_Q^K(I-E)||_(2->2)
 <=rho_K+K sqrt(||H||_infinity).                        (APLIP4)
```

The estimate is independent of the number and weights of occurrences,
matrix dimension, and multiplicity.  Individual adjoint actions may remain
operator-distance two on sparse corners; only their normalized common row
square enters.

