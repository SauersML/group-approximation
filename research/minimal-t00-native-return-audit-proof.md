---
rg: 2
id: minimal-t00-native-return-audit-proof
kind: route
title: Multiply the two nested chains by t00 and exhaust their signed-L0 endpoint returns
target: minimal-t00-conversion-cannot-return-native-whitehead-root
requires:
  - fused-cross-returns-cancel-positive-l0-gauge
  - signed-l0-does-not-attach-cross-returns-to-order-seven-head
  - native-whitehead-corner-collapses-hecke-flags
---

The root paths in the first chain are

```text
(4,7)(7,9)=(4,9),       (8,4)(4,9)=(8,9),             (TCRP1)
```

and their coefficient product is `b_2r=s_00t_0=x_1`.
The second uses

```text
(7,9)(9,5)=(7,5),       (7,5)(5,8)=(7,8),             (TCRP2)
```

and `b_3a_2=s_000t_00=x_2`.  This proves `(TCR2)`.

Prefix cancellation gives

```text
(s_00t_0)t_00=s_00t_000,
t_00(s_000t_00)=s_0t_00,
t_1(s_1t_00)=t_00,                                    (TCRP3)
```

proving `(TCR5)`.  A commutator multiplying on the right of the first root
must use a path `(8,9)(9,ell)=(8,ell)`; multiplying on the left of the
second uses `(ell,7)(7,8)=(ell,8)`.  The inequalities on `ell` are exactly
the conditions that both elementary roots be defined and distinct.

For `(TCR6)`, close the ten constant signed-`L_0` generators to their exact
`8192`-element matrix group.  For each of the five first-row and five
second-row spare endpoints, conjugate the corresponding constant rank-one
transvection by all group elements and compare with the native target
transvection.  Coefficients play no role in this root-position test.  Every
comparison set is empty, proving the ten zero-conjugator assertions.
