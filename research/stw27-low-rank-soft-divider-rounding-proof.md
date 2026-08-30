---
rg: 2
id: stw27-low-rank-soft-divider-rounding-proof
kind: route
title: Squeeze every fibre rank into one integer and detect the first rank-jumping witness
target: stw27-low-rank-soft-divider-rounding
requires:
  - stw27-coordinate-euler-slack-obstructs-compact-dividers
artifacts:
  - research/artifacts/stw27-soft-divider-hinge-audit-2026-08-30.md
---

Represent `y` by a positive element `a in C(X) tensor K`.  Evaluation at
each `z in X` is a Cuntz-semigroup morphism.  If

```text
r(z)=rank(a(z)),
```

then the two comparisons give

```text
ceil(M/(n+1)) <= r(z) <= floor(M/n).                  (2)
```

The real interval in `(2)` has length

```text
M/n - M/(n+1) = M/(n(n+1)) < 1.
```

It therefore contains at most one integer.  Existence of `y` forces such an
integer `r` to exist, and `(2)` forces `r(z)=r` at every point.

The eigenvalue functions of a norm-continuous compact-operator-valued
positive function are continuous.  Since `a(z)` has rank exactly `r`, its
`r`-th eigenvalue is positive everywhere and its `(r+1)`-st eigenvalue is
zero everywhere.  Compactness of `X` gives a uniform spectral gap below the
`r`-th eigenvalue.  Functional calculus therefore produces a continuous
rank-`r` support projection `q` with `[a]=[q]`.  Thus `y` is compact.  Cuntz
comparison between projection classes is Murray--von Neumann comparison, so
the two inequalities are precisely the asserted subbundle relations.

For sharpness, set `U=(0,1]`, let `h(t)=t`, and let

```text
Y=C([0,1])^n direct_sum C_0(U).
```

Represent `Y` by the positive element `diag(1_n,h)`. Then

```text
n[Y]=[diag(1_(n^2),h,...,h)] <= (n^2+n)[1],

(n^2+n)[1] <= (n+1)[Y].
```

The first comparison holds because a positive contraction in a unital
corner is Cuntz below the corner unit (use its square root); the second holds
because `(n+1)Y` has the constant module of rank `n(n+1)` as a direct
summand. To see noncompactness directly, the classes

```text
y_k=[diag(1_n,(h-1/k)_+)]
```

increase to `[Y]`. If `[Y]<<[Y]`, then `[Y]<=y_k` for some `k`; evaluation
at any `t in (0,1/k)` gives the impossible rank inequality `n+1<=n`.

Finally, in the mod-prime coordinate-Hopf situation, the first part turns
any alleged divider into a projection class.  The Chern calculation in
`stw27-coordinate-euler-slack-obstructs-compact-dividers` then contradicts
the displayed coordinate threshold.
