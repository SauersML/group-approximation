---
rg: 2
id: affine-auxiliary-control-flow-barrier-proof
kind: route
title: Affine solution spaces remain affine under coordinate projection
target: affine-auxiliary-control-flow-barrier
requires: []
artifacts:
  - research/artifacts/meta-recursive-qca-audit-2026-08-22.md
---

The full solution set

```text
L = {(x,y) : A x + B y = c}
```

is either empty or an affine subspace of `F_2^(m+k)`. Coordinate projection
`pi(x,y)=x` is an affine map, so `R=pi(L)` is affine. Equivalently, if
`x_1,x_2,x_3` lie in `R`, choose witnesses `y_1,y_2,y_3`; then

```text
A(x_1+x_2+x_3)+B(y_1+y_2+y_3)
 = c+c+c
 = c
```

over `F_2`, so `x_1+x_2+x_3` is again in `R`.

For one-hot control with `m>=3`, the visible relation contains `e_1,e_2,e_3`
but not `e_1+e_2+e_3`, hence is not affine. For path activation `t=a AND b`,
the relation contains

```text
(0,0,0), (1,0,0), (0,1,0)
```

but their ternary affine sum `(1,1,0)` is not in the AND graph. Therefore
neither relation has an existential affine encoding.

For controlled reflection, the valid points `000`, `010`, and `100` have
ternary affine sum `110`, while `110` violates `y=cx`. The same projection
argument therefore rules out arbitrary hidden commuting parity auxiliaries.
