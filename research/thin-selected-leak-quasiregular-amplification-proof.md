---
rg: 2
id: thin-selected-leak-quasiregular-amplification-proof
kind: route
title: Lazify the selected coefficient and take a slow diagonal tensor power
target: thin-selected-leak-amplifies-to-codense-quasiregular-profile
requires: []
---

The selected coefficient

```text
phi(g)=<alpha(g)v,v>
      =tau(v^* pi(g)v pi(g)^*)                         (1)
```

is positive definite and satisfies `phi(g)=1` exactly when
`alpha(g)v=v`.  In particular its `1`-level stabilizer is the subgroup `H`
in `(QRA1)`.  Since `v` is `C`-fixed but not `A`-fixed, `C<=H<A`.
Profinite density of `C` makes every containing subgroup, including `H`,
profinite dense.

Lazify the coefficient by

```text
theta(g)=(1+phi(g))/2.                                 (2)
```

It is the coefficient of `1 direct_sum alpha` at
`2^(-1/2)(1 direct_sum v)`.  For `g in H`, `theta(g)=1`.  For `g notin H`,
the equality case of Cauchy--Schwarz gives `|theta(g)|<1`.  Hence

```text
theta(g)^k -> 1_H(g).                                  (3)
```

Represent `alpha` at coordinate `n` by the adjoint superoperators
`Ad U_n` on the finite-dimensional Hilbert--Schmidt space.  Direct sum with
the trivial representation and take a tensor power `k_n`.  Tensor-product
defects grow at most linearly in `k_n`.  By passing to a diagonal sequence,
choose `k_n->infinity` slowly enough that

```text
k_n times (presentation defect at n) -> 0
```

and, on the first `n` enumerated group elements, `k_n` times the coordinate
coefficient error also tends to zero.  The resulting tensor powers are
normalized-HS asymptotic representations, and their distinguished vector
coefficients converge pointwise to `(3)`.  This proves `(QRA2)`.
