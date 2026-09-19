---
rg: 2
id: agent-stw77-zero-near-witnesses-descend-properness-proof
kind: route
title: Compress approximate lifts and polar-normalize their row
target: agent-stw77-zero-near-witnesses-descend-properness
requires: []
---

Choose `b_i in B` with

```text
||pi(b_i)-w_i||<delta<1/4
```

for one common `delta`.  Replace `b_i` by `x_i=p b_i p`.  Since
`w_i=q w_i q`, faithfulness and contractivity of compression give

```text
||pi(x_i)-w_i||<delta.                                 (1)
```

Regard

```text
X=[x_1 x_2],       W=[w_1 w_2]
```

as row operators over the corners `pBp` and `qB(H)q`.  From `(1)`,

```text
||pi^(1,2)(X)-W|| <= sqrt(2) delta.                    (2)
```

The exact orthogonality relations say `W^*W=1_(M_2) tensor q`.  Since
`||W||=1` and `||X||<=1+sqrt(2)delta`, `(2)` yields

```text
||X^*X-1_(M_2) tensor p||
 <=2 sqrt(2)delta+2delta^2
 <1.                                                   (3)
```

Here faithfulness of the matrix amplification of `pi` was used to read the
same norm in `M_2(B)`.  Thus `X^*X` is invertible in
`M_2(pBp)`.  Set

```text
Y=X(X^*X)^(-1/2)=[y_1 y_2].                            (4)
```

Then `Y` is a row isometry:

```text
y_i^*y_j=delta_(i,j)p.                                 (5)
```

Each `y_i` belongs to `pBp`.  Formula `(5)` gives isometries with initial
projection `p`, and their range projections are orthogonal because

```text
(y_i y_i^*)(y_j y_j^*)=y_i(y_i^*y_j)y_j^*=0
```

for `i!=j`.  Their ranges lie below `p`, proving that `p` is properly
infinite.

For the final assertion of the claim, if a splitting pair for the amplified
Toeplitz--Cuntz defect were within `1/4` of the represented algebra, the
argument above would make the original finite defect properly infinite,
contradicting `eT_2e=C e`.
