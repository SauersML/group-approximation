---
rg: 2
id: simple-map-restriction-rigidity-proof
kind: route
title: Apply Malcev and the normal-kernel left-right intertwiner representation
target: simple-map-quotient-has-rigid-fd-restriction
requires: []
---

Let `rho:Q->U(d)` be nontrivial. Simplicity makes `rho` injective. Its image
is a finitely generated linear group, hence residually finite by Mal'cev, so
`Q` is residually finite and therefore sofic, contrary to the hypothesis.
Thus every finite-dimensional representation of `Q` is trivial.

For `u|K=v|K`, the identity lies in `V=Hom_K(v,u)`. If `T in V`, `f in F`
and `k in K`, then `f^(-1)kf in K` and

```text
u(k)u(f)T v(f)^*
 =u(f)u(f^(-1)kf)T v(f)^*
 =u(f)T v(f)^*v(k).
```

So `V` is `F`-invariant. For `k in K`, `Pi(k)T=T`, so the action factors
through `Q` and is trivial. Applying it to `I in V` yields `u(f)=v(f)`.
