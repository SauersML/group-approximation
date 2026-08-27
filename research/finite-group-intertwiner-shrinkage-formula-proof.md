---
rg: 2
id: finite-group-intertwiner-shrinkage-formula-proof
kind: route
title: Isotypic Schmidt supports compute the exact shrunk-space deficiency
target: finite-group-intertwiner-shrinkage-formula
requires: []
---

By complete reducibility,

```text
K = directSum_lambda (I_(S_lambda) tensor
                       Hom(C^(m_lambda),C^(n_lambda))).   (1)
```

Fix `X<=V`.  For each `lambda`, let `L_lambda<=S_lambda` be the left Schmidt
support of the projection of `X` to the `lambda`-isotypic summand: equivalently,
`L_lambda` is spanned by all contractions

```text
(id tensor phi)(x),
```

with `x` in that projected subspace and `phi` a linear functional on
`C^(m_lambda)`.  Put `r_lambda=dim L_lambda`.

Every vector of the projected `X` lies in

```text
L_lambda tensor C^(m_lambda),
```

so, since a subspace of a direct sum has dimension at most the sum of the
dimensions of its coordinate projections,

```text
dim X <= sum_lambda r_lambda m_lambda.                 (2)
```

On the other hand `(1)` gives exactly

```text
K(X) = directSum_lambda
       (L_lambda tensor C^(n_lambda)).                 (3)
```

Indeed the inclusion from left to right is immediate.  Conversely, if
`s=(id tensor phi)(x)` is one of the contractions generating `L_lambda` and
`w in C^(n_lambda)`, apply the rank-one multiplicity map

```text
v |-> phi(v) w
```

to `x`; this produces `s tensor w`.  Hence every vector on the right side of
`(3)` is in `K(X)`.

Therefore

```text
dim X-dim K(X)
 <= sum_lambda r_lambda (m_lambda-n_lambda)
 <= sum_lambda d_lambda (m_lambda-n_lambda)_+.          (4)
```

Equality is attained by taking

```text
X = directSum_(m_lambda>n_lambda)
    S_lambda tensor C^(m_lambda).
```

For this choice, `r_lambda=d_lambda` exactly on the positive-excess blocks and
zero elsewhere, proving `(FGS1)`.

Finally, if `dim V=dim W`, then

```text
sum_lambda d_lambda(m_lambda-n_lambda)=0.
```

The total positive weighted excess therefore equals the total negative
weighted excess and is one half of the weighted `L1` distance.  This is
`(FGS2)`.
