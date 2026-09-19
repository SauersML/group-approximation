---
rg: 2
id: stabilized-cross-braid-coefficient-proof
kind: route
title: Multiply the complementary three-coordinate Whitehead blocks
target: stabilized-cross-braid-has-s3-square-gauge-fence
requires:
  - cross-branch-partial-whiteheads-have-finite-wreath-gauge-model
  - two-distinct-rank-two-channels-cannot-factor-cross-return
---

Use ordered coordinates `(7,8,9)`.  The first two factors are

```text
P_0=[[q_1,0,q_0],[0,1,0],[q_0,0,q_1]],
Q_0=[[1,0,0],[0,q_0,r],[0,p,q_1]].                    (SCBP1)
```

Multiplying `P_0Q_0P_0` gives

```text
[[q_1,p,0],[r,q_0,0],[0,0,1]],                        (SCBP2)
```

which is `K_0` stabilized by the ninth coordinate.  Multiplication in the
other order gives the same block, proving the first braid in `(SCB3)`.
Replacing `q_0,p,r` by `q_1,r,p` gives the `i=1` identity.

The products between an `i=0` and the opposite `i=1` packet reduce using

```text
q_0q_1=q_1q_0=0,
q_0p=p, p q_1=p, q_1r=r, r q_0=r,                    (SCBP3)
```

with all reverse mismatches zero.  This proves the cross commutations in
`(SCB4)`.

Complementary diagonal idempotents add to one, so the first fusion is
`w_79(1)`.  On `(8,9)`, the `Q` blocks are

```text
Q_0=[[q_0,r],[p,q_1]],       Q_1=[[q_1,p],[r,q_0]].   (SCBP4)
```

Their product is

```text
[[0,p+r],[p+r,0]]=w_89(u).                            (SCBP5)
```

The identical coarse calculation on `(7,8)` gives
`K_0K_1=w_78(u)`.  Since conjugating a coordinate Weyl by the constant
`(7,9)` swap moves the pair `(8,9)` to `(8,7)`, `(SCB6)` follows.

Finally, the assignments `(SCB7)` put the two complementary braid packets
in separate `S_3` factors.  Same-factor Coxeter braid relations and
different-factor commutations verify the entire table.  Fusion gives the
diagonal packet `(SCB8)`, whose first two reflections have a three-cycle
product.  This proves the finite gauge fence.
