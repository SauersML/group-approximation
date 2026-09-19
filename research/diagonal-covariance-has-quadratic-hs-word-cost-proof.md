---
rg: 2
id: diagonal-covariance-has-quadratic-hs-word-cost-proof
kind: route
title: Reorder the difference shift and telescope its commutators
target: diagonal-covariance-has-quadratic-hs-word-cost
requires:
  - diagonal-covariance-synchronizes-hnn-and-bcs-shifts
---

Normalized Hilbert--Schmidt distance is bi-invariant. The standard telescoping
inequalities give

```text
||[c,U^j]-I||_2 <= j epsilon_0,
||[c,U^j z U^(-j)]-I||_2 <= 2j epsilon_0+epsilon_z.       (1)
```

Indeed `[c,U]` is conjugate to `[t,U]` or its inverse, and conjugating a
product changes it by at most the sum of the changes of its factors.

Since `t=cU`, commuting each `U` past the later copies of `c` transforms
`(cU)^n` into `c^nU^n` using `n(n-1)/2` adjacent swaps. Hence

```text
||(cU)^n-c^nU^n||_2 <= n(n-1)epsilon_0/2.               (2)
```

Conjugation by two unitaries at distance `eta` differs on any unitary by at
most `2eta`. Apply this to `(2)`. Then telescope conjugation of
`U^n z U^(-n)` by the `n` copies of `c` and use `(1)` with `j=n`. The total
is at most

```text
n(n-1)epsilon_0+n(2n epsilon_0+epsilon_z)
 <= 4n^2epsilon_0+n epsilon_z,
```

which is `(DCH1)`.

