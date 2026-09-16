---
rg: 2
id: nucdim-factor-transfers-m-comparison
kind: claim
title: A separable tensor factor of nuclear dimension at most m turns almost unperforation into m-comparison
distinct_from:
  stw99-lxxv-fnd-implies-pure: that concerns algebras which themselves have finite nuclear dimension; this transfers comparison from an arbitrary (possibly nonnuclear, nonseparable) factor with almost unperforated Cuntz semigroup through a finite-nuclear-dimension factor.
artifacts:
  - research/artifacts/nucdim-factor-comparison-divisibility-2026-09-16.md
---

Let `A` be a C*-algebra whose Cuntz semigroup `Cu(A)` is almost unperforated,
and let `B` be a separable C*-algebra with `dim_nuc B <= m`.  Then
`Cu(A tensor_min B)` has `m`-comparison: whenever
`x, y_0, ..., y_m in Cu(A tensor_min B)` and, for each `j`, some `k_j in N`
satisfies `(k_j+1) x <= k_j y_j`, then

```text
x <= y_0 + y_1 + ... + y_m .
```

No exactness, nuclearity or separability is assumed on `A`.  For `A = C` this
is Robert's theorem that nuclear dimension at most `m` gives `m`-comparison.
