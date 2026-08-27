---
rg: 2
id: random-private-dual-distance-proof
kind: route
title: Union-bound all short dependencies among random labels
target: independent-private-labels-have-growing-dual-distance
requires: []
---

For a fixed nonempty set `S`, independence and uniformity give

```text
Pr[sum_(t in S)v_t=0]=2^(-r).
```

Put `w_0=floor(r/(8 log_2 r))`.  For all sufficiently large `r` (depending
only on `C`),

```text
log_2(eK/w_0) <= 2 log_2 r.
```

Hence

```text
Pr[there is a dependency of weight <=w_0]
 <=2^(-r) sum_(w=1)^w_0 binom(K,w)
 <=2^(-r) w_0 (eK/w_0)^w_0
 <=2^(-r/2).
```

This proves `(IPD1)`.  The failure probability can be added to the vanishing
failure probability in the private Weyl metric-entropy sampling argument.
For recursive selection, test every one of the finitely many subsets of size
at most `w_0` in addition to the real-quantifier-elimination gap predicate.
