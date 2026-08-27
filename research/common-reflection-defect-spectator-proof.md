---
rg: 2
id: common-reflection-defect-spectator-proof
kind: route
title: Compress every complete context transport to the invariant accepting corner
target: common-reflection-defect-is-holonomy-spectator
requires: []
---

Since the source partition sums to `q`, its transported partition sums to
`WqW^*`.  By hypothesis the target partition also sums to `q`, so
`WqW^*=q`.  Multiplying on the right by `W` gives `Wq=qW`.  As `e=p-q` and
`W` commutes with the unit `p` of `pAp`, it also commutes with `e`.

It follows that

```text
(qWq)(qW^*q)=qWW^*q=q,
(qW^*q)(qWq)=q,                                           (RHS2)
```

so `qWq` is a corner unitary.  For any sequence `W_1,...,W_r` satisfying
the same condition, all `q` projections commute through all `W_i`, whence

```text
q W_1 ... W_r q=(qW_1q)...(qW_rq).                        (RHS3)
```

Thus the accepting-corner return map is independent of every operation on
the complementary `e` block.  This proves the claimed spectator statement.

For the stronger compression assertion, suppose `U` is unitary and `qUq`
is unitary relative to `q`.  Then

```text
0=q-(qUq)^*(qUq)=qU^*(1-q)Uq.                            (RHS4)
```

The right side is `((1-q)Uq)^*((1-q)Uq)`, so faithfulness gives
`(1-q)Uq=0`.  Applying the same argument to `(qUq)(qUq)^*=q` gives
`qU(1-q)=0`.  Therefore `Uq=qUq=qU`.  Group-algebra corners sit faithfully
in their finite group von Neumann algebras, so the conclusion applies to all
of the algebraic packets considered here.
