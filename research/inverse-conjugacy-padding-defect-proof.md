---
rg: 2
id: inverse-conjugacy-padding-defect-proof
kind: route
title: Match multiplicities on each inverse pair and swap the paired eigenspaces
target: inverse-conjugacy-padding-equals-multiplicity-defect
requires: []
artifacts:
  - research/artifacts/retained-core-and-rank-countertests-2026-09-08.md
---

## Proof

Write `R^ = R (+) R_new` and `m = m_(R^)`.

**Lower bound.**  A self-adjoint unitary `X^` is its own inverse, so `(IC1)`
says `R^` and `R^(-1)` are unitarily equivalent, hence
`m(lambda) = m(lambda^(-1))` for every `lambda`.  Fix a pair
`{lambda, lambda^(-1)}` with `lambda != +-1` and put
`delta = m_R(lambda) - m_R(lambda^(-1))`.  Then

```text
m_(R_new)(lambda^(-1)) - m_(R_new)(lambda) = delta,
```

so `m_(R_new)(lambda) + m_(R_new)(lambda^(-1)) >= |delta|`.  Summing over the
pairs, all of which occupy disjoint parts of the spectrum of `R_new`,
`k = dim R_new >= k_min(R)`.

**Upper bound.**  Take `R_new` with `m_(R_new)(lambda) = max(-delta, 0)` and
`m_(R_new)(lambda^(-1)) = max(delta, 0)` for each pair, and nothing on `+-1`;
then `dim R_new = k_min(R)` and `m(lambda) = m(lambda^(-1))` for every
`lambda`.  For each pair choose a unitary `W : E_lambda -> E_(lambda^(-1))`
between the (now equidimensional) eigenspaces of `R^` and define

```text
X^ (u, v) = (W^* v, W u)     on   E_lambda (+) E_(lambda^(-1)),
X^ = 1                       on   E_1 (+) E_(-1).
```

Then `X^` is unitary and `X^^2 = 1`, hence self-adjoint, and

```text
X^ R^ X^ (u, v) = X^ (lambda W^* v, lambda^(-1) W u)
                = (lambda^(-1) u, lambda v) = R^(-1)^ (u, v),
```

while on `E_(+-1)` both sides are `+-1`.  So `(IC1)` holds with
`k = k_min(R)`.
