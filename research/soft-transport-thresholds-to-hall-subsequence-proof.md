---
rg: 2
id: soft-transport-thresholds-to-hall-subsequence-proof
kind: route
title: Threshold at half the dual gap and use finite pigeonhole
target: soft-transport-thresholds-to-hall-subsequence
requires: []
---

Put `t=gamma/2` and define the cheap-edge graph

```text
E_n={(u,v): c_n(u,v)<t}.
```

First, `E_n` cannot support any transport plan with marginals `alpha,beta`.
Indeed, if `nu` were such a plan supported on `E_n`, then dual feasibility in
`(STH1)` would give

```text
gamma
 <= sum_v alpha_v x_n(v)+sum_u beta_u y_n(u)
 =  sum_(u,v) (x_n(v)+y_n(u)) nu(u,v)
 <= sum_(u,v) c_n(u,v) nu(u,v)
 < t=gamma/2,
```

a contradiction.  By the weighted Hall/max-flow criterion, there is therefore
some `S_n subset V` with

```text
alpha(S_n)>beta(N_(E_n)(S_n)).                         (STH5)
```

Second, every edge outside `E_n` has cost at least `t`.  Hence

```text
t * sum_((u,v) notin E_n) mu_n(u,v)
 <= sum_(u,v) c_n(u,v) mu_n(u,v),
```

so `(STH2)` implies

```text
sum_((u,v) notin E_n) mu_n(u,v) -> 0.                 (STH6)
```

There are only finitely many pairs `(E,S)` because `V,W` are fixed finite
sets.  Pass to an infinite subsequence on which `(E_n,S_n)=(E,S)` is
constant.  Then `(STH5)` becomes the fixed strict Hall deficit `(STH3)` and
`(STH6)` becomes `(STH4)`.

No quantitative lower bound on the positive Hall deficit is needed for this
subsequence statement.  If desired, fixed positive rational weights give one
automatically because only finitely many cuts exist.