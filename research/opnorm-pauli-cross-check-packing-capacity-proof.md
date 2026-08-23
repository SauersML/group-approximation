---
rg: 2
id: opnorm-pauli-cross-check-packing-capacity-proof
kind: route
title: Compare one same-site commutator with one cross-site commutator and pack the unitary group
target: opnorm-pauli-cross-check-packing-capacity
requires: []
---

For unitaries `X,Z,W`, the commutator word is 2-Lipschitz in its second
argument:

```text
||[X,Z]-[X,W]||_op <= 2 ||Z-W||_op.                           (PPL1)
```

Indeed, after inserting `X Z X^-1 W^-1`, the two resulting differences each
have norm `||Z-W||_op`.

Fix `i!=j`. By `(PPC1)--(PPC3)` and `(PPL1)`,

```text
beta
 <= ||J-I||_op
 <= ||J-[X_i,Z_i]||_op
    + ||[X_i,Z_i]-[X_i,Z_j]||_op
    + ||[X_i,Z_j]-I||_op
 <= 2 epsilon + 2 ||Z_i-Z_j||_op.
```

Hence

```text
||Z_i-Z_j||_op >= (beta-2 epsilon)/2 = delta,
```

which proves pairwise separation.

The compact metric space `U(d)` has finite `delta`-packing number, proving
`(PPC5)`. For the explicit estimate, identify `M_d(C)` with real Euclidean
space of dimension `2 d^2` using Frobenius norm. Operator-norm separation by
`delta` implies Frobenius separation by at least `delta`, while every unitary
has Frobenius norm `sqrt(d)`. The Euclidean balls of radius `delta/2` around
the `Z_i` are disjoint and lie in the ball of radius `sqrt(d)+delta/2`.
Comparing volumes gives

```text
N (delta/2)^(2 d^2)
 <= (sqrt(d)+delta/2)^(2 d^2),
```

which is `(PPC6)`.
