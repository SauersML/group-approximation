---
rg: 2
id: atlas-common-u-second-moment-is-one-projection-gram-proof
kind: route
title: Expand a product of two reflections and telescope its square
target: atlas-common-u-second-moment-is-one-projection-gram
requires:
  - atlas-a4-classical-opaque-star-sharp-constant
---

Write `P=P_t`, `Q=Q_t`, `R=2Q-1`, and `S=2P-1`.  Then `V_t=RS`.  Direct
expansion, using `P^2=P`, `Q^2=Q`, and tracial cyclicity, gives

```text
||RSRS-1||_2^2
 =||RS-SR||_2^2
 =16||QP-PQ||_2^2
 =32[tau(PQ)-tau(PQPQ)].                              (1)
```

The spectrum of a product of two reflections is invariant under complex
conjugation, so `tau((RS)^2)` is real.  Since `RSRS` is unitary,

```text
||RSRS-1||_2^2=2-2 tau((RS)^2).                       (2)
```

Combining `(1)` and `(2)` proves `(A4-GRAM-2)`.

For `(A4-MOM-ORBIT)`, let `B=A V_t A^*`.  Tracial invariance gives
`tau(B^2)=tau(V_t^2)`, while telescoping and unitary invariance give

```text
|tau(V_s^2)-tau(B^2)|
 <=||V_s^2-B^2||_2
 <=2||V_s-B||_2.
```

Take the infimum over `A`.  Finally, on a left-regular group unitary
`lambda(g)`, `tau(lambda(g)^2)` equals one exactly when `g^2=1` and zero
otherwise.  The order profiles and collision norm from
`atlas-a4-classical-opaque-star-sharp-constant` give the stated sharp finite
calibration.
