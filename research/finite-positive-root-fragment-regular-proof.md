---
rg: 2
id: finite-positive-root-fragment-regular-proof
kind: route
title: Close a finite positive-root fragment inside a finite nilpotent algebra group
target: finite-positive-root-fragments-have-marked-regular-models
requires:
  - leavitt-range-sum-fold-is-first-object-erasing-row
---

Write the finitely many chosen unitriangular generators as `g_i=I+X_i`.
Every product of `n` strictly upper-triangular `n by n` matrices is zero,
even when their entries lie in a noncommutative ring.  Hence the span `B` in
`(FPR2)` is closed under multiplication, finite-dimensional over `F_p`, and
satisfies `B^n=0`.

The identities

```text
(I+X)(I+Y)=I+(X+Y+XY),
(I+X)^(-1)=I-X+X^2-...+(-1)^(n-1)X^(n-1)              (FPP1)
```

show that `1+B` is a group and contains every `g_i` and inverse.  Since `B`
is a finite-dimensional vector space over a finite field, `1+B` is finite.
It is a `p`-group because it is a finite algebra group over `F_p`.

The elementary-root map is faithful in each coordinate:

```text
x_ij(r)=I+rE_ij=I       iff       r=0.                 (FPP2)
```

Thus `(FPR5)` is nonidentity.  Every stipulated fragment relator is already
an equality of the literal matrices in `U_n^+(R)`, so restriction to `H` and
then the left regular representation preserves it exactly.  A nonidentity
regular translation has trace zero, proving `(FPR6)`.

Finally `x_ij(A)^k=x_ij(kA)` and the additive characteristic is `p`, so a
nonzero root has order `p`.  Left multiplication by it partitions `H` into
`p`-cycles.  On each cycle all `p`th roots of unity occur once, proving the
equal phase multiplicities and `(FPR7)`.
