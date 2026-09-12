---
rg: 2
id: stw82-two-by-two-colour-reuse-quantitative-obstruction-proof
kind: route
title: Use the two-colour pigeonhole and support perturbation estimates
target: stw82-two-by-two-colour-reuse-quantitative-obstruction
requires:
  - stw82-indivisible-order-zero-reuse-is-graph-colouring
---

Let `h'_i=alpha'_i(1)` and `k'_i=beta'_i(1)`.  Evaluation at the unit and
(T2) give

```text
norm(h_i-h'_i)<=delta,       norm(k_i-k'_i)<=delta.     (T4)
```

Whenever two perturbed maps have the same global colour, their supports are
orthogonal by the direct-sum support criterion.  Thus, for example, if
`alpha'_i` and `beta'_j` have the same colour, then

```text
norm(h_i k_j)
 <= norm((h_i-h'_i)k_j)+norm(h'_i(k_j-k'_j))
 <= 2 delta.                                           (T5)
```

The same estimate applies to two `alpha` supports or two `beta` supports.

There are now only three cases.  If `alpha'_0,alpha'_1` receive the same
colour, (T5) gives `norm(h_0h_1)<=2 delta`.  If
`beta'_0,beta'_1` receive the same colour, it gives
`norm(k_0k_1)<=2 delta`.  Otherwise both pairs use both colours.  Up to
interchanging the two colour labels, the `beta` pair either has the same
orientation as the `alpha` pair or the opposite orientation.  In the first
case both `h'_0 k'_0` and `h'_1 k'_1` vanish; in the second both
`h'_0 k'_1` and `h'_1 k'_0` vanish.  Applying (T5) to the two pairs shows
that the corresponding maximum in (T1) is at most `2 delta`.

In every case at least one of the four entries defining `mu` is at most
`2 delta`.  This is exactly (T3).  The argument permits the colour
assignment and the perturbed maps to depend arbitrarily on the approximation
stage.
