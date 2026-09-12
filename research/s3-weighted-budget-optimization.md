---
rg: 2
id: s3-weighted-budget-optimization
kind: claim
title: The weighted S3 detector optimization collapses to one square-root scalar
---

For `A,B>=0`, not both zero, put

```text
lambda(p,q)=p+q-sqrt(p^2-pq+q^2).
```

Then

```text
sup_(p,q>0) lambda(p,q)/(pA+qB)
 = 3 / (2(A+B+sqrt(AB))).                              (S3-WOPT)
```

When `A,B>0`, the supremum is attained.  With `q=1`, one maximizing ratio is

```text
p = sqrt(B)(2sqrt(A)+sqrt(B))
    / (sqrt(A)(sqrt(A)+2sqrt(B))).                     (S3-WOPT-R)
```

At `A=0` or `B=0` the same formula holds by the corresponding limiting choice
of weights.

Thus all freedom in the weighted two-generator Cayley gap can be eliminated
analytically: a pair of upper energy budgets `(A,B)` defeats a required
commutant-distance floor exactly when the single scalar
`A+B+sqrt(AB)` is small enough.