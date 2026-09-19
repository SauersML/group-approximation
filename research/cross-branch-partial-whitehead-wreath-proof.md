---
rg: 2
id: cross-branch-partial-whitehead-wreath-proof
kind: route
title: Multiply the two partial branch swaps and exchange the S3 factors
target: cross-branch-partial-whiteheads-have-finite-wreath-gauge-model
requires:
  - complementary-private-weyl-loops-have-s3-square-gauge-model
  - binary-branch-flip-weyl-has-s3-c2-model
---

The Leavitt products in `(CBW1)` follow immediately from
`t_is_j=delta_(ij)` and `q_0+q_1=1`.  On the ordered root coordinates
`(7,8)`, the first partial Whitehead is

```text
K_0=[[q_1,p],[r,q_0]],                                 (CBWP1)
```

and the second is the complementary block

```text
K_1=[[q_0,r],[p,q_1]].                                 (CBWP2)
```

Using `(CBW1)`, direct block multiplication proves that both are
involutions, commute, and have product

```text
[[0,u],[u,0]]=w_78(u),                                 (CBWP3)
```

which proves `(CBW3)`.

Conjugating the elementary blocks in `(CBW4)` by `(CBWP3)` swaps root
directions and sends each coefficient `q_i` to `uq_iu=q_(1-i)`.  This gives
`(CBW5)` and hence the aggregate rows `(CBW6)`.

For the finite model, conjugation by `c=(1 3)` sends `a=(1 2)` to
`b=(2 3)`, sends `b` to `a`, and fixes `c`.  Therefore the automorphism
`phi` is involutive and the semidirect product `(CBW8)` is finite.
Substitution proves every row in `(CBW5)--(CBW10)`.  Since `ca` is a
three-cycle, `(CBW11)` has order three.  The central extension in `(CBW12)`
then verifies the two-factor partial-Whitehead gauge table.
