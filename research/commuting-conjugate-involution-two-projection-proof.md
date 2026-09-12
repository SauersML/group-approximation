---
rg: 2
id: commuting-conjugate-involution-two-projection-proof
kind: route
title: Reduce the native lamp transfer to one balanced projection overlap
target: commuting-conjugate-involution-is-balanced-overlap
requires: []
---

Round the almost self-adjoint involution `c` by functional calculus; this
changes every displayed fixed word by `o(1)`.  For the rounded involution set

```text
P=(1-c)/2,       Q=hPh*.
```

The commutation of `c` with `hch*` is equivalent to `[P,Q]=0`.  Since
`tr(c)=0`, both projections have trace `1/2`.  Put `a=tr(PQ)`.  Expanding
gives

```text
c h c h*=(1-2P)(1-2Q)=1-2P-2Q+4PQ,
tr(c h c h*)=4a-1.                                    (PRO1)
```

Because the factors commute, the four atoms have traces

```text
tr(PQ)=tr((1-P)(1-Q))=a,
tr(P(1-Q))=tr((1-P)Q)=1/2-a.                           (PRO2)
```

Hence

```text
1-|tr(c h c h*)|^2=8a(1-2a).                          (PRO3)
```

Also

```text
||P-Q||_2^2=1-2a,
||P+Q-I||_2^2=2a,                                     (PRO4)
```

so projective scalarity is exactly the invariance/complement dichotomy.

For the firewall, take the Bernoulli probability space on `{+1,-1}^(A/C)`.
The base coordinate and its `h`-translate are independent because `hC!=C`.
Their `-1` projections commute, have trace `1/2`, and intersection trace
`1/4`.  The stabilizer `C` fixes the base coordinate.  This proves `(CCI8)`
inside the exact crossed product.

Finally, the universal RCC dilation does not preserve the new hypothesis.
For `v=[[0,u],[u*,0]]` and `D=diag(h,h)`, the two products

```text
v(DvD*) = diag(u h u* h*, u* h u h*),
(DvD*)v = diag(h u h* u*, h u* h* u),                  (PRO5)
```

need not agree.  Thus `(CCI2)` genuinely removes the generic dilation
counterexample.  What remains is to exclude the interior value `a=1/4`
specifically in matrix ultraproducts with the arithmetic regular marginal;
property-(T) or finite-dimensional codensity must act on the COMMON atom
projections in `(PRO2)`, not on the two marginal commutants separately.
