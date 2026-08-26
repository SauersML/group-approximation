---
rg: 2
id: cross-row-native-diamond-cube-locks-moving-gauge
kind: route
title: Lock the common moving gauge with the two cross-row native-arm commutators
target: el20-six-moving-coefficient-square-bridges
requires:
  - reverse-return-has-native-arm-leavitt-diamond
  - b2-b3-pair-full-hecke-four-native-sectors
  - endpoint-whitehead-star-braid-synchronizes-native-gauges
---

Dead route.  Besides the two rowwise native-arm diamonds, use the literal
cross commutators

```text
[x_98(t_00),x_87(s_00)]=x_97(1),
[x_86(s_00),x_28(t_00)]=x_26(1).
```

These relations genuinely mix the two coefficient rows.  The hoped
inference was that the resulting commutator cube, together with the
`J_1--J_2` braid and the two order-seven heads, would force the synchronized
Whitehead gauge to be trivial.

`cross-row-native-diamond-cube-retains-common-c2-gauge` shows that the
complete displayed interface has an exact central `C_2` symmetry.  Dress
both `J_i` and both `B_(i+1)` by the same central involution.  Each
order-seven product `J_iB_(i+1)A_i` is unchanged; every rowwise and
cross-row commutator is unchanged; the B2/B3 Hecke sign flips are unchanged;
and the braid merely confirms that the two Whitehead dressings are equal.

Thus the cross cube synchronizes no more than the already known common
gauge.  A live continuation needs an odd occurrence of exactly one of
`J_i,B_(i+1)`, or a common-carrier typing which forbids the paired dressing.
