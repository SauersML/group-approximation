---
rg: 2
id: atlas-strict-s3-ceiling-from-five-row-phase-lift
kind: route
title: Spend the five saturated phase rows below the 19243 floor
target: atlas-two-s3-energy-ceiling-below-19243-floor
requires:
  - atlas-five-row-operator-phase-lift
  - atlas-boundary-tangent-covariance-coercivity
  - atlas-19243-centrality-is-bar-s-consequence
---

The five-row form of the established global covariance coercivity gives

```text
a(U)^2+b(U)^2 <= sum_(j in J)l_j(U)^2.                 (FPR1)
```

Apply `(FPL4)`.  Every fixed boundary word `s_j` and the interior word
`c_19243` lie in the normal closure of the canonical packet `bar_S`.
Choose fixed van Kampen expressions and let `L_j,L_int` be their numbers of
conjugates of packet relators.  If

```text
delta(U)=max_(s in bar_S)||pi_U(s)-1||_2,              (FPR2)
```

then telescoping gives

```text
e_j(U)<=L_j delta(U),             e_int(U)<=L_int delta(U).
```

Hence, with the fixed constant

```text
M_5=C_5 [sum_(j in J)L_j^2+L_int^2],                  (FPR3)
```

equations `(FPR1)--(FPL4)` imply

```text
a(U)^2+b(U)^2 <= M_5 delta(U)^2.                       (FPR4)
```

Take `eta=1/256` and any

```text
0<delta_0<1/(16 sqrt(M_5)).                            (FPR5)
```

Then `delta(U)<delta_0` gives `a(U)^2+b(U)^2<eta<1/128`,
which is exactly the target ceiling.
