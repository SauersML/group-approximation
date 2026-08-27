---
rg: 2
id: hnn-type-projection-leakage-proof
kind: route
title: Expand the projection and apply Britton normal form once
target: hnn-type-projection-leakage
requires: []
---

Write `p=sum_(k in K) a_k k`.  In

```text
t p t^(-1) p=sum_(h,k in K) a_h a_k t h t^(-1) k,
```

Britton normal form says a summand can equal the identity only if `h in H`.
It then reduces to `theta(h)k`, which is the identity exactly when
`k=theta(h)^(-1)`.  Hence

```text
tau(t p t^(-1)p)
 =sum_(h in H) a_h a_(theta(h)^(-1))
 =tau(theta(E_H(p))p),
```

proving `(HTL1)`.  Both `p` and `tpt^(-1)` are projections of trace `tau(p)`.
The tracial inner product of two projections is real and nonnegative, so
expanding their squared `L^2` distance gives `(HTL2)`.

Equality in `(HTL2)` is equivalent, by faithfulness of the canonical trace,
to `tpt^(-1)=p`.  If this equality holds, every coefficient `a_k` with
`k notin H` must vanish: its term `t k t^(-1)` is a reduced HNN normal form
outside the base group and cannot cancel a base-group term.  Therefore
`p in C[H]`, after which the equality reads `theta(p)=p`.  The converse is
one defining HNN relation extended linearly.  This proves `(HTL3)`.

If `H={1}`, then `E_H(p)=tau(p)1`; substituting this in `(HTL2)` gives
`(HTL4)`.
