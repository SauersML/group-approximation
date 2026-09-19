---
rg: 2
id: faithful-atlas-free-loeb-proof
kind: route
title: Compare a fixed root with one moved atlas coordinate
target: faithful-sofic-action-atlas-has-free-loeb-actor
requires: []
---

Use the ultraproduct form of a sofic action.  Write `Omega` for the Loeb root
space, `sigma(g)` for the pmp permutation induced by `g`, and

```text
pi:X->X_U
```

for the equivariant atlas map.  Represent `pi(x)` by a measurable label
function `f_x` on `Omega`.  GKEP equivariance and distance-one separation
say

```text
f_(gx)(omega)=f_x(sigma(g)^(-1)omega)  almost everywhere,   (FLP1)
mu{f_x=f_y}=0                           whenever x!=y.       (FLP2)
```

Fix `g!=e`.  Faithfulness supplies `x` with `gx!=x`.  If
`sigma(g)omega=omega`, then `(FLP1)` gives

```text
f_(gx)(omega)=f_x(omega)
```

outside a null set.  By `(FLP2)` the equality set on the right is null.
Therefore `Fix(sigma(g))` is null.  Intersecting the conull sets over the
countable group proves essential freeness and `(FLA1)`.

For `(FLA2)`, its kernel is the normal core

```text
core_A(C)=intersection_(a in A) a C a^(-1).
```

The core is a normal subgroup of `A=SL_3(Z[1/2])` contained in the
infinite-index lattice `C=SL_3(Z)`.  The normal subgroup theorem for this
higher-rank S-arithmetic group makes it finite central rather than finite
index.  The center of `SL_3(Z[1/2])` is trivial (a scalar of determinant one
in this ring is `1`), so the core is trivial.  The arithmetic action is
faithful, and the general argument applies.

