---
rg: 2
id: prefix-order-seven-pair-retains-gl7-mark
kind: claim
title: Both prefix order-seven anchors retain the GL7 marked model
artifacts:
  - research/prefix-order-seven-pair-gl7-proof.md
  - experiments/prefix_order_seven_pair_gl7_audit.py
distinct_from:
  literal-prefix-coupling-of-j1-j2-has-gl7-model: that authenticates both native adjacent swaps and the prefix compilation but does not add either odd order-seven Hecke head; this folds both heads into the same finite triangle.
  native-whitehead-hecke-head-has-order-seven-anchor: that proves each exact order-seven relation in the elementary group and its scalar-gauge coercivity; this proves their simultaneous authenticated-prefix packet still has an exact finite marked model.
  quarter-whiteheads-lack-unequal-source-conjugacy: that identifies the two mixed source-conjugacy rows which would force the rank contradiction; this shows that even both odd anchors do not supply either row.
---

**ESTABLISHED TWO-ANCHOR FINITE FENCE.**  Retain the authenticated literal
prefix triangle

```text
X_1=x_87(x_1), Y_1=x_78(y_1),
X_2=x_98(x_2), Y_2=x_89(y_2),
J_i=X_iY_iX_i,
J_1J_2J_1=J_2J_1J_2.                                 (P71)
```

Adjoin both native Hecke heads

```text
v_1=B_2A_1,       [B_2,A_1]=X_1,
v_2=B_3A_2,       [B_3,A_2]=X_2,
(J_1v_1)^7=(J_2v_2)^7=1.                              (P72)
```

The union still has an exact marked model in the same `GL_7(F_2)` chart.
Keep the prefix triangle on `(7_0,9,8_0)` and put the two Hecke heads on
the adjacent triangles `(6,7_0,8_0)` and `(10,8_0,9)`:

```text
X_1=e_(8_0,7_0), Y_1=e_(7_0,8_0),
X_2=e_(9,8_0),   Y_2=e_(8_0,9),
A_1=e_(6,7_0), B_2=e_(8_0,6),
A_2=e_(10,8_0), B_3=e_(9,10).                        (P73)
```

Then the two path commutators in `(P72)` are `X_1,X_2`.  Direct
multiplication gives both seventh powers in `(P72)`, while `J_1,J_2` are
the adjacent transpositions `(7_0 8_0)` and `(8_0 9)`.  The marked child on
the disjoint vertices `(7_1,8_1)` remains nonidentity.

Thus the odd anchors eliminate independent scalar or commuting involution
gauges attached to either displayed head, but they do not authenticate the
source ranks `1/2,1/4` or a one-eighth target label.  In particular, adding
both anchors to the literal prefix braid remains equal-type finite `S_3`
geometry.  The smallest surviving rank compiler is still the pair of mixed
source-conjugacy occurrences isolated by
`quarter-whiteheads-lack-unequal-source-conjugacy`; equivalently one must
prove the two finite-coordinate source-return leakage estimates, not add
another fixed prefix or seventh-power relation.

This is a scoped model of the displayed occurrence table, not a
representation of the full binary Leavitt elementary group.  No Property
T, Kazhdan input, literature theorem, trace assumption, local computation,
or Lean compilation is used.

DERIVATION
prefix-order-seven-pair-gl7-proof
