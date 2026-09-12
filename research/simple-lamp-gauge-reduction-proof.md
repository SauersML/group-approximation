---
rg: 2
id: simple-lamp-gauge-reduction-proof
kind: route
title: Put an independent actor approximation in the lamp commutant and audit regular absorption
target: simple-lamp-gauge-rigidity-reduces-to-actor-classicalization
requires: []
---

Because the matrices `1 tensor v_g` commute with the entire left regular
lamp algebra, substituting `(SGR2)` in `(SGR1)` preserves lamp covariance.
The permutation implementers multiply according to the actor automorphisms,
so the remaining product error is exactly the product error of `v`.  Trace
factorization gives the canonical-trace assertion.

For `(SGR4)`, on a regular orbit indexed by actor elements compute

```text
(lambda(g) tensor pi(g))(delta_h tensor pi(h) xi)
 = delta_(gh) tensor pi(gh) xi.
```

Thus the inverse of the displayed basis change conjugates
`lambda tensor pi` to `dim(pi)` copies of `lambda`.  The same calculation is
valid on the injective local charts of a sufficiently free sofic
approximation.  This proves both the reduction and the fixed-twist
absorption fence.
