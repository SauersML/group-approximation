---
rg: 2
id: triangular-generator-column-minrank-proof
kind: route
title: Repeat basis columns privately and force a triangular identity block
target: degree-one-generator-columns-have-sqrt-minrank-but-no-gap
requires: []
---

The appended block has `r(r+1)/2=O(n)` columns, so total length remains
`Theta(n)`.  If the original evaluation code has weight at least `delta K_0`
on every nonzero functional, appending `K_1=O(n)` coordinates leaves relative
weight at least

```text
delta K_0/(K_0+K_1)>0.
```

Thus both column measures retain uniform spectral gaps.

Every sampled equation is exactly `(DGM2)`.  The specified leading block is
lower triangular with diagonal one regardless of its unspecified entries
below the diagonal, proving rank at least `r`; the leading identity block
proves attainability.

For robustness, `B=0` proves `(DGM3)`.  After arbitrary diagonal repetition,
use `k` nearly equal blocks.  Each all-one block has rank one, so total rank is
at most `k`.  All diagonal signs are correct.  Among the strict upper-triangle
zero constraints, the fraction inside blocks is

```text
sum_t binom(|C_t|,2)/binom(r,2)<=1/k+o(1).
```

Factoring this `B` gives the claimed `k`-qubit exact additive Weyl model.
