---
rg: 2
id: order-twelve-long-head-return-proof
kind: route
title: Identify seven Leavitt summands and multiply the returned binary matrices
target: order-twelve-long-head-return-exposes-an-eighth-atom-involution
requires:
  - four-cell-marked-star-has-an-eighth-head-flag
  - head-square-whitehead-loop-preserves-deep-star-flag
---

First compute the star support.  The stabilizer action of
`P=H_2H_1` has fourth power equal to the identity on the center/sign
quotient.  Its cube has source conditions `Z_2=-1,Z_3=+1` and range
conditions `Z_2=+1,Z_3=+1`.  Applying `H_3` adds `Z_4=+1` and changes the
range third sign to `Z_3=-1`.  This gives the source and range stated after
`(OTR2)`.  The swap action of `U_2` then proves that `K` reduces `S`.

For the exact word calculation, use the seven right-module summands

```text
e_1@7, q@4, e_2@8, q@5, e_3@9, q@6, e_4@10,          (1)
```

in that order.  The coefficients `a_i,b_i` identify consecutive summands.
After these identifications, `H_1,H_2,H_3` are the consecutive two-step
unitriangular heads on the chain

```text
1--2--3--4--5--6--7.
```

The word `U_2` is the permutation `(3 5)(4 6)`.  Direct multiplication over
`F_2` gives the following columns for `K`:

```text
1 |-> 1+2+3+4+7,       2 |-> 2+5,
3 |-> 5+6,             4 |-> 3+4+6+7,
5 |-> 3+4+7,           6 |-> 4+7,          7 |-> 7. (2)
```

Cubing `(2)` gives

```text
1 |-> 1+2+3+4,         2 |-> 2+7,
3 |-> 5+6,             4 |-> 3+4+5+6,
5 |-> 5,               6 |-> 3+5,          7 |-> 7. (3)
```

Squaring `(3)` fixes columns `2,...,7` and sends `1` to `1+7`.  Undoing
the module identifications, the map `1->7` has coefficient

```text
b_4a_1=s_(0000)t_0.
```

This proves `K^6=X_14` on `(1)`.  Away from `(1)`, every head and partial
Whitehead is the identity; the only remaining action is the outer swap of
the equal complementary pieces of coordinates `5,6`, which has order two.
Thus `(OTR3)` holds globally.  Since `K^6!=1` and `(2)` has fourth power
nonidentity, `K` has order exactly twelve.

On the same block, `H_14` is the three-node head

```text
1 |-> 1+2+7,        2 |-> 2+7,        j |-> j (j>=3). (4)
```

Its square sends `1` to `1+7` and fixes the other columns, proving
`(OTR5)`.  Its inverse sends `1` to `1+2`, `2` to `2+7`, and fixes the
remaining columns.  Multiplying `(3)` by this inverse gives

```text
D:
1 |-> 1+3+4+7,       2 |-> 2,
3 |-> 5+6,           4 |-> 3+4+5+6,
5 |-> 5,             6 |-> 3+5,          7 |-> 7.   (5)
```

Squaring `(5)` gives the identity.  This proves `(OTR6)` and also shows
that `D` commutes with the first elementary arm `1->2`, namely `A_1`.
The center/sign conjugation formulas show that `K^3` and `H_14` each flip
`Z_1` on `S`; hence `D` fixes `Z_1` there.  Since `A_1,Z_1` generate the
remaining Pauli factor, Schur decomposition gives `(OTR7)`.

Finally `Y_14` is the reverse transvection `7->1`, and `J_14` swaps
summands `1,7`.  Multiplying either matrix by `(5)` gives an element whose
cube is a nonidentity involution and whose sixth power is one.  Hence both
orders are six on `(1)`.  On the complementary summands `D` is only the
outer coordinate swap and `Y_14,J_14` are the identity, so their orders
still divide six.  This proves `(OTR9)` and completes the fence.
