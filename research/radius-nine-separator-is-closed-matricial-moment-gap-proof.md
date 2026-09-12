---
rg: 2
id: radius-nine-separator-is-closed-matricial-moment-gap-proof
kind: route
title: Use direct-sum convexity, strong separation, and rational perturbation
target: radius-nine-separator-is-closed-matricial-moment-gap
requires:
  - tracial-npa-cannot-separate-canonical-trace
---

All coordinates in `(R9-DUAL-1)` are uniformly bounded: trace moments lie in
`[-1,1]`, and each unitary relator defect squared lies in `[0,4]`.  The closure
is therefore compact.

If `U` and `V` have dimensions `d` and `e`, normalized trace on `U direct_sum V`
gives the convex combination with weights `d/(d+e)` and `e/(d+e)` in every
moment coordinate and in `D`.  Repeated amplification realizes every rational
convex weight.  Approximating arbitrary weights by rationals and taking the
closure shows that `K_9^mat` is convex.

Suppose `g_9` is outside this compact convex set.  Strong finite-dimensional
separation gives an affine real functional `L` and a margin `2c_0>0` such that,
after shifting its constant term,

```text
L(x)>=0       (x in K_9^mat),
L(g_9)<=-2c_0.
```

Because `K_9^mat union {g_9}` is bounded, approximate all coefficients of `L`
closely by rationals and increase the rational constant term by the uniform
approximation error.  The resulting rational functional is nonnegative on
`K_9^mat` and remains at most `-c_0` on `g_9`.  If its coefficient of `D` is
not positive, increase that coefficient to any positive rational number.
Since `D>=0` everywhere and `D(g_9)=0`, this preserves both inequalities.
Writing the other coordinates as the rational trace polynomial `P` gives
`(R9-DUAL-3)`, after replacing `c_0` by a smaller positive rational.

Conversely `(R9-DUAL-3)` is nonnegative on the generating set and hence on
its closure, while it is negative at `g_9`; therefore `g_9` is outside.

Finally, membership of `g_9` in the closure is by definition equivalent to a
sequence whose combined coordinate vector converges to `g_9`.  Its last
coordinate is precisely `D`, giving the truncated-microstate formulation.
The canonical group moments satisfy every tracial NPA constraint, so `g_9`
lies in the tracial body even when it misses `K_9^mat`.  This proves that the
separation, if present, cannot come from a dimension-blind tracial dual.

