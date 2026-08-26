---
rg: 2
id: marked-star-asymmetric-head-support-proof
kind: route
title: Intersect the star character with one and two uncancelled b-head returns
target: marked-star-asymmetric-heads-have-half-quarter-sources
requires:
  - marked-star-outer-corrected-whiteheads-are-quarter-swaps
  - native-whitehead-hecke-head-has-order-seven-anchor
---

Write the three star centers as

```text
C_1=x_42(q),              C_2=x_52(q),
C_3=x_62(q),              C_iE=-E.                    (1)
```

Let `D_2=x_84(b_2)` and `D_3=x_95(b_3)`.  The only star-center
commutators are

```text
[D_2,C_1]=Z_2=x_82(b_2),
[D_3,C_2]=Z_3=x_92(b_3).                              (2)
```

Indeed `b_iq=b_i`; all other root rectangles are noncomposable.  The
anchored arms `Z_2,Z_3` commute with the three centers and are independent
Pauli `Z` operators on `E`.  The A-head factors `x_47(a_1),x_58(a_2)`
reduce `E`.  It follows from `(2)` that

```text
E meet H_1EH_1^(-1)=E(1+Z_2)/2.                       (3)
```

The same projection is obtained with `H_1` replaced by `H_1^(-1)`, because
`x_47(a_1)` commutes with `Z_2` and every center.  The two conjugate cuts
commute with `E`, so, for `T_1=EH_1E`,

```text
T_1^*T_1=T_1T_1^*=E(1+Z_2)/2.                         (3')
```

Pauli balance gives relative rank `1/2`.  The identical calculation for
`H_2` gives `E(1+Z_3)/2`.

For the cumulative head, conjugation by `H_2` sends

```text
C_2 |-> Z_3C_2,
Z_2 |-> Z_3C_2Z_2,                                    (4)
```

because `[x_58(a_2),Z_2]=C_2` and `D_3` then sends
`C_2` to `Z_3C_2`.  Starting from the `H_1`-moved condition
`Z_2C_1=-1`, equations `(1)` and `(4)` show that the range intersection
requires

```text
Z_3=+1,                     Z_2=-1.                   (5)
```

Thus the range support is `R_-+`.  In the inverse order, `H_1` fixes
`C_2,Z_3`, while its own moved `C_1` condition requires `Z_2=+1`.
Therefore the source support is `R_++`.  The two commuting independent
Pauli signs have four equal atoms on `E`, proving `(ASH4)` and its quarter
rank.

Finally, the braid in the prerequisite applies to `U_i=L_iJ_i`.  It does
not type `J_i` alone on the star Pauli algebra:
`J_iA_iJ_i^(-1)` is the forked arm with unchanged outer index.  Nor does
`H_i` reduce `E`; equations `(3)--(5)` show precisely the lost half.  Hence
the exact uncompressed relation `(J_iH_i)^7=1` cannot be compressed to an
identity among the star polar parts without an additional leakage theorem.

If individual head polars are provisionally written with reservoir factors
`W_1,W_2`, their composition on `R_++` has factor `W_2W_1`.  Even granting
the extra, currently unproved identifications `W_i=V_i`, adjacent
transpositions `V_1,V_2` in `S_3` satisfy the braid and are conjugate while
`V_2V_1` is a three-cycle.  This proves that the braid cannot identify the
cumulative quarter holonomy with the second involutive gauge and completes
the scoped fence.
