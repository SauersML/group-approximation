---
rg: 2
id: asymmetric-prefix-unit-hecke-frame-proof
kind: route
title: Expand the moved quarter signs and isolate the root-position obstruction
target: asymmetric-prefix-unit-misses-fixed-hecke-frame
requires:
  - asymmetric-prefix-unit-conjugates-native-whiteheads
  - b2-b3-pair-full-hecke-four-native-sectors
  - native-whitehead-hecke-head-has-order-seven-anchor
---

In the diagonal word `D`, coordinates `7,8` carry `u` and all coordinates
appearing in `(AUF2)` except `8` carry the identity.  Hence

```text
DrD^(-1)=x_58(a_2u^(-1)),       DlD^(-1)=l.           (1)
```

Using the inverse in `(APU1)`, prefix cancellation gives

```text
a_2u^(-1)
=s_1t_00(s_0t_00+s_10t_01+s_11t_1)
=s_1t_000=a_3;                                         (2)
```

the last two summands vanish because `t_00s_1=0`.  The cycle `P` sends
`(5,8)` to `(5,9)` and `(6,9)` to `(6,7)`, proving `(AUF3)`.

For completeness, the directed root positions generating the fixed source
are

```text
H: 65,54,42,       d:82,       f:94,       k:92,
c:97,              v:57,       w:67,       s:68,
r:58,              l:69.                              (3)
```

Every extra positive root produced by Steinberg collection follows a
directed path in this graph.  There is no directed path from vertex `5` to
vertex `9`, so position `59` is absent from the collected subgroup.  This
proves the first statement after `(AUF5)` without making a coefficient
specialization.

The native Whitehead actions in
`native-whitehead-corner-collapses-hecke-flags` give `(AUF6)`.  For the
Singer comparison, the exact order-seven blocks are

```text
M_1=J_1B_2A_1 on {4,7,8},
M_2=J_2B_3A_2 on {5,8,9}.                              (4)
```

The root `omega_3=x_67(a_3)` is disjoint from the second block and is fixed
by it.  Under the first block its row `6` stays fixed and its column remains
in `{4,7,8}`.  Thus no power in `(4)` carries `omega_3` to the original
position `69`.  Each factor in `(AUF7)` commutes with `omega_3` by the
ordinary nonincident/same-column Steinberg relations, proving the bare
Hecke statement.

Finally, multiplying `D` by further elementary torus words changes only
the diagonal coefficient units.  It cannot change the coordinate
permutation of a conjugated root.  A coordinate permutation carrying the
ordered Whitehead pair `(8,7)` to `(9,8)` must satisfy `(AUF8)`.  If it also
preserves the fixed signed center-chain occurrence, it normalizes the
directed path

```text
6 -> 5 -> 4 -> 2.                                      (5)
```

The directed path has no nonidentity vertex automorphism, so all four
vertices in `(5)` are fixed.  The image of `(5,8)` is therefore inevitably
`(5,9)`.  This proves the diagonal-extension obstruction.
