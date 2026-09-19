---
rg: 2
id: orbitwise-scalar-relator-quotient-proof
kind: route
title: Restrict the ambient action to the cyclic hull of the coherent fibre
target: orbitwise-scalar-relators-give-quotient-representation
requires: []
---

Because `pi(g^-1 r_j g)` is unitary and its compression in `(ORQ2)` is the
unitary scalar `lambda_j P`, equality in Schwarz implies that `P H` reduces
`pi(g^-1 r_j g)` and the restriction is `lambda_j`.

For `xi in P H`, therefore,

```text
pi(r_j)pi(g)xi
 =pi(g)pi(g^-1 r_j g)xi
 =lambda_j pi(g)xi.                                    (ORQ5)
```

By density, every `r_j` acts by `lambda_j` on `K`.  The space `K` is
`pi(F)`-invariant and hence reducing, so `pi|_K` factors through `(ORQ3)`.
It is nonzero because `P H` is nonzero.  Finally centrality of `J` and
`(ORQ1)` give

```text
pi(J)pi(g)xi=pi(g)pi(J)xi=-pi(g)xi,
```

so `J=-I_K`.
