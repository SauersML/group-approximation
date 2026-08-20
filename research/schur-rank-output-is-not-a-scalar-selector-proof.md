---
rg: 2
id: schur-rank-output-is-not-a-scalar-selector-proof
kind: route
title: Characters evaluate selector words as affine parities
target: schur-rank-output-is-not-a-scalar-selector
requires: []
---

Every word in the elementary abelian group `D` has the form

```text
w=z_1^a_1 ... z_k^a_k,                 a_i in F_2.
```

On the character indexed by `x`, its sign is

```text
(-1)^(sum_i a_i x_i),
```

or, after allowing multiplication by the fixed central sign, an affine
parity. This cannot equal `(-1)^f(x)` on the Boolean cube when `f` is
nonaffine. The Schur construction avoids this calculation only because it
places `f` in the rank of a commutation matrix; its restriction multiplicity
is an integer in the representation category, not the value of a group word.

