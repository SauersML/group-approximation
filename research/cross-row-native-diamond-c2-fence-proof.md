---
rg: 2
id: cross-row-native-diamond-c2-fence-proof
kind: route
title: Dress both native Whiteheads and both Hecke arms by one central involution
target: cross-row-native-diamond-cube-retains-common-c2-gauge
requires:
  - reverse-return-has-native-arm-leavitt-diamond
  - b2-b3-pair-full-hecke-four-native-sectors
  - endpoint-whitehead-star-braid-synchronizes-native-gauges
---

The ordinary Steinberg commutator law and prefix cancellation give

```text
[x_98(t_00),x_87(s_00)]=x_97(t_00s_00)=x_97(1),
[x_86(s_00),x_28(t_00)]=x_26(t_00s_00)=x_26(1),      (1)
```

where the second row is the reverse adjacent-root commutator; in
characteristic two its usual minus sign is immaterial.  These are
`(CDC1)`.

Let `c` be a central involution and perform `(CDC3)`.  For every element
`g`,

```text
(hc)g(hc)^(-1)=hgh^(-1),        [hc,g]=[h,g].         (2)
```

Equation `(2)` proves invariance of the two diamond conjugacies, every
returned commutator arm, and the B2/B3 sign-flip conjugacies.  It also shows
that the two cross commutators in `(1)`, whose factors are already returned
arms, remain literally unchanged.

Because `c` is an involution, the dressed `J_i,B_(i+1)` remain involutions.
Centrality gives `(CDC4)`, so both complete head words and their seventh
powers remain unchanged.  Finally

```text
(J_1c)(J_2c)(J_1c)=J_1J_2J_1 c,
(J_2c)(J_1c)(J_2c)=J_2J_1J_2 c,                      (3)
```

and the original Coxeter row makes `(3)` equal.  Choosing `c!=1` proves
the claimed exact symmetry and the surviving common gauge.
