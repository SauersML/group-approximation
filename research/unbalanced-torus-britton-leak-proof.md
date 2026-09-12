---
rg: 2
id: unbalanced-torus-britton-leak-proof
kind: route
title: Commute the central letter through the two torus factors and compare with the Britton trace
target: unbalanced-torus-word-localizes-britton-leak
requires:
  - two-torus-closures-detect-denominator-multiplicity
---

Write

```text
D_12=A_12 (H B_21 H^*) A_12 W_12^*,
D_23=A_23 (H B_32 H^*) A_23 W_23^*,                  (UBP1)
```

where `A_ij=X_(x_ij(p))`, `B_ji=X_(x_ji(-1))`, and
`W_ij=X_(w_ij(1))`.  Conjugating a transported root by `T` and then by
`H^*` gives the exact equality

```text
||T(HB_jiH^*)T^*-HB_jiH^*||_2
 =||T_1B_jiT_1^*-B_ji||_2.                             (UBP2)
```

The product telescope and the definition of `eta_L` therefore give

```text
||T D_12 T^*-D_12||_2<=3 eta_L+eta_21,
||T D_23 T^*-D_23||_2<=3 eta_L+eta_32,                 (UBP3)
```

and hence, for `D=D_12D_23`,

```text
||TDT^*-D||_2<=6 eta_L+eta_21+eta_32.                  (UBP4)
```

Since `ev(R_tor)=H^*D`, unitary invariance says

```text
||D-H||_2=eta_R.                                       (UBP5)
```

Insert `D` twice into `THT^*-H`, use `(UBP4)--(UBP5)`, and obtain
`(UBL2)`.

Finally `W=[T,H]=THT^*H^*` satisfies

```text
||THT^*-H||_2^2=||W-I||_2^2
 =2-2 Re tr(W)>=2(1-eta_B).                            (UBP6)
```

Combining `(UBL2)` and `(UBP6)` proves `(UBL3)`.  Canonical microstates make
`eta_R,eta_L,eta_B` tend to zero, so the sum of the two nonnegative root
defects has liminf at least `sqrt(2)`; their maximum has liminf at least
`1/sqrt(2)`, proving `(UBL4)`.
