---
rg: 2
id: primitive-native-hecke-relators-have-no-odd-mixed-occurrence
kind: claim
title: The primitive native and Hecke relators have no odd mixed occurrence
invalidates:
  - primitive-menu-odd-native-hecke-coercivity
artifacts:
  - research/primitive-native-hecke-relator-occurrence-audit-proof.md
  - GroupApproximation/Steinberg/Basic.lean
  - GroupApproximation/Leavitt/FinitePresentation.lean
distinct_from:
  native-whitehead-hecke-head-has-order-seven-anchor: that discovers a derived odd order-seven identity in the group; this audits only the primitive Steinberg triangles and coefficient relations, and explicitly does not deny that derived identity.
  projective-row-data-do-not-authenticate-hecke-polars: that gives an abstract spectator countermodel for square, support, and separate covariance data; this audits the literal source relators and locates the unmatched odd factors.
  mark-fixed-relative-words-do-not-coerce-native-hecke-kernel: that treats the old mark-fixed relative words; this explains why the primitive menu gives no individual odd row, before the derived order-seven identity is used.
---

**ESTABLISHED PRIMITIVE-RELATOR OCCURRENCE AUDIT.**  In the literal chained
packet write

```text
A_1=x_47(a_1),      A_2=x_58(a_2),
B_1=x_72(b_1),      B_2=x_84(b_2),      B_3=x_95(b_3),
X_1=x_87(s_(00)t_0),       Y_1=x_78(s_0t_(00)),
X_2=x_98(s_(000)t_(00)),   Y_2=x_89(s_(00)t_(000)).   (PMO1)
```

The two native partial Whitehead words and unequal-scale Hecke words are

```text
J_1=X_1Y_1X_1,             J_2=X_2Y_2X_2,
u_1=B_2A_1,                u_2=B_3A_2A_1.             (PMO2)
```

The explicit Steinberg presentation has root additivity, nonincident-root
commutation, and adjacent-root multiplication relators.  Among the named
packet letters, the only primitive adjacent relations mixing Hecke arms
with a native Whitehead coefficient are

```text
[B_2,A_1]=X_1,             [B_3,A_2]=X_2.             (PMO3)
```

Equivalently,

```text
(B_2A_1)^2=X_1,            (B_3A_2A_1)^2=X_2.         (PMO4)
```

They authenticate exactly the factors occurring **twice** in `J_i`.  The
only odd primitive Whitehead factors are `Y_1,Y_2`, and neither occurs in
an unequal-scale Hecke word or mixed adjacent triangle among the named
arms.  All root factors in `(PMO1)--(PMO2)` have indices in

```text
K={2,4,5,6,7,8,9},                                    (PMO5)
```

disjoint from the marked indices `{1,3}`, so their primitive relations with
`z=x_13(q)` are commutations.  The six coefficient-ring equations contain
no root position or occurrence carrier.

This exhausts the **primitive displayed relators**, not their group-theoretic
consequences.  In particular it is fully consistent with the subsequently
established derived identities

```text
(J_1u_1)^7=1,                 (J_2u_2A_1)^7=1,         (PMO6)
```

from `native-whitehead-hecke-head-has-order-seven-anchor`.  Those are the
first genuine odd native/Hecke anchors and move the live problem from
occurrence parity to compression leakage.  The formal Steinberg group is
presented by relation schemas, while finite presentability is obtained
abstractly from the coefficient-ring presentation; no canonical finite
Tietze list is emitted for a stronger exhaustive syntax claim.

DERIVATION
primitive-native-hecke-relator-occurrence-audit-proof
