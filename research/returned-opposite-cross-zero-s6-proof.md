---
rg: 2
id: returned-opposite-cross-zero-s6-proof
kind: route
title: Put the two returned branch Whiteheads on disjoint Coxeter triples
target: returned-opposite-cross-zero-has-finite-s6-model
requires:
  - relative-a2-weyl-orbit-has-seven-state-gauge-model
  - reverse-product-whitehead-fold-has-finite-fusion
---

Write the positive and opposite elementary blocks as

```text
x(q_1)=[[1,q_1],[0,1]],       y(q_0)=[[1,0],[q_0,1]].
```

Both products of their off-diagonal parts vanish, so the unipotents commute.
This proves `(ROC1)` and, after exchanging zero and one, its companion.

For the finite model, adjacent transpositions obey

```text
(1 2)(2 3)(1 2)=(2 3)(1 2)(2 3)=(1 3),               (1)
```

and the same identity on `{4,5,6}` gives `W_1=(4 6)`.  Elements supported
on the two disjoint triples commute.  Hence `C_0C_1=J`, both equations in
`(ROC4)` hold, and

```text
W_0W_1=(1 3)(4 6)=W_A.                                (2)
```

The parent pair `J=(1 2)(4 5)`, `D_A=(2 3)(5 6)` is the coordinatewise
product of the two adjacent-transposition pairs, so `(1)` proves both parent
factorizations.  All listed elements are involutions and `J` is nonidentity.
A cyclic permutation of three copies supplies the order-three relative orbit
and exact return.  The left regular representation then has every displayed
defect zero and `||lambda(J)-1||_op=2`.

