---
rg: 2
id: kazhdan-projection-norm-limit-of-averages-proof
kind: route
title: Powers of a lazy symmetric average converge to the Kazhdan projection
target: kazhdan-projection-is-norm-limit-of-finite-averages
requires: []
artifacts:
  - research/artifacts/shorter-proofs-review-2026-09-07.md
---

## Proof

Let `S = S^(-1)` be a finite Kazhdan generating set with constant `kappa` and
put

```text
a = (1/2)(1 + (1/|S|) sum_(s in S) u_s)  in  C*_max(L).
```

In every unitary representation `pi` of `L`, decompose the space into the
`L`-invariant vectors and their orthogonal complement, both `pi(L)`-invariant.
On the invariant vectors `pi(a) = 1`.  On the complement, property (T) gives
`max_(s in S) ||pi(s)xi - xi|| >= kappa ||xi||`, so the self-adjoint operator
`(1/|S|) sum_s pi(s)` has norm at most `1 - delta` there for a `delta > 0`
depending only on `|S|` and `kappa`, and the laziness keeps the spectrum away
from `-1`, so `||pi(a)|xi|| <= (1 - delta/2)||xi||` on the complement.

The bound is uniform over all unitary representations, so in `C*_max(L)`

```text
||a^n - e_L|| <= (1 - delta/2)^n,
```

since `a^n - e_L` acts as `0` on invariant vectors and as `pi(a)^n` on the
complement.  Each `a^n` is a finitely supported probability average, being a
product of such.  Take `F = supp(a^n)` and `mu` its weights for `n` large.
