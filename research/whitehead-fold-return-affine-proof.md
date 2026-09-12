---
rg: 2
id: whitehead-fold-return-affine-proof
kind: route
title: Factor both native Whiteheads from the four affine arm transvections
target: whitehead-fold-return-has-affine-model
requires:
  - full-fold-compose-return-has-finite-affine-model
---

Use the ordered basis `(A,C,R_0,R_1)` and the actors from `(FAR2)`.  On the
three-dimensional subspace relevant to branch zero, direct substitution
gives

```text
W_0(A)=R_0,             W_0(R_0)=A,
W_0(C)=C+A+R_0,         W_0(R_1)=R_1.                  (1)
```

For branch one it gives

```text
W_1(A)=R_1,             W_1(R_1)=A,
W_1(C)=C,               W_1(R_0)=R_0.                 (2)
```

Equations `(1)--(2)` show immediately that `W_i^2=1` and prove `(WFR4)`.
The two transvections on the plane `<A,R_i>` are the elementary shears

```text
S_i:A |-> A+R_i,             T_i:R_i |-> R_i+A.       (3)
```

The extra action of `S_0` on `C` is the same `R_0` shear and does not change
the calculation.  Evaluating both sides on the displayed basis gives

```text
S_iT_iS_i=T_iS_iT_i=W_i.                              (4)
```

Conjugating `(4)` by the involution `W_i`, or checking on the basis once
more, yields both root-swap equations in `(WFR3)`.

For the cross-branch row, equations `(1)--(2)` give on the four basis
vectors

```text
W_0W_1W_0(A)=A,
W_0W_1W_0(C)=C+R_0+R_1,
W_0W_1W_0(R_0)=R_1,
W_0W_1W_0(R_1)=R_0,                                   (5)
```

and the same four values result from `W_1W_0W_1`.  This proves `(WFR5)`.
The commutator computations `(WFR1)` and `(WFR6)` are exactly `(FAR3)`, so
all appearances of `S_i,T_i` in the factorization and in the two-step table
are literally the same elements.

Finally, in the finite character packet of `(FAR5)--(FAR6)`, conjugation by
`g in GL(V)` sends `D_v` to `D_(gv)`.  Applying this to `(1)--(2)` proves

```text
W_iD_AW_i^(-1)=D_(R_i),
W_iD_(R_i)W_i^(-1)=D_A.                               (6)
```

Every coordinatewise payload and opposite-root identity from the finite
`GL_5(F_2)` packet is preserved by the same permutation action.  Since
`D_A` is nonidentity, its left regular representation has
`||lambda(D_A)-1||_op=2`, while every displayed discrepancy is zero.
