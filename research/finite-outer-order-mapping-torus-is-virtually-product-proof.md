---
rg: 2
id: finite-outer-order-mapping-torus-is-virtually-product-proof
kind: route
title: Correct a power of the stable letter by its inner implementer
target: finite-outer-order-mapping-torus-is-virtually-product
requires:
  - mf-is-commensurability-invariant
---

Choose `r>=1` and `a in K` with `phi^r=Inn(a)`.  If `t` is the stable
letter, then

```text
s = a^(-1) t^r
```

centralizes `K`: for every `k in K`,

```text
s k s^(-1) = a^(-1) phi^r(k) a = k.
```

The exponent of `s` is `r`, so `s` has infinite order and
`<s> intersection K={1}`.  Hence `H=<K,s>` is isomorphic to `K x Z`.
The exponent map shows that `H` is the preimage of `rZ<=Z`, so
`[G:H]=r`.

If `K` is MF, then `K x Z` is MF.  The finite-index permanence theorem
`mf-is-commensurability-invariant` makes `G` MF as well, proving `(FO1)` by
contraposition.
