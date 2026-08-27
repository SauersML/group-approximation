---
rg: 2
id: a4-alternating-projections-amplify-line-carrier
kind: claim
title: Alternating C3 and C2 projections amplify an A4 line carrier at rate one third per round
---

In a multiple of the regular `A4` representation, fix a `C3` character
projection `P=P_chi`, the positive `C2` projection `Q=Q_+`, and the line carrier
`E=E_chi` from `a4-line-carriers-explicit-idempotents`.  Then for every integer
`m>=1`,

```text
(P Q P)^m = E + 3^(-m) (P-E).                          (A4-POWER)
```

Consequently

```text
||(PQP)^m-E||_op = 3^(-m)
```

and, for normalized Hilbert--Schmidt norm,

```text
||(PQP)^m-E||_2^2 = 1/(4*9^m).                         (A4-HS-POWER)
```

The constants are independent of the number of regular copies.

Thus the positive-density A4 line carrier can be isolated to arbitrary fixed
accuracy by a **bounded-depth alternating-projection word**, with exponential
error decay and no dimension-dependent spectral calculation.  Since `P` and
`Q` themselves are fixed Fourier averages of the order-three and order-two
context generators, this gives a finite polynomial amplifier for the hidden
operator-valued label carried by each regular A4 context.