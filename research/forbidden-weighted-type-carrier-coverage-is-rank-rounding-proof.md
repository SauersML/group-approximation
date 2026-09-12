---
rg: 2
id: forbidden-weighted-type-carrier-coverage-is-rank-rounding-proof
kind: route
title: Trim each forbidden marked type to four-divisible rank
target: forbidden-weighted-type-carrier-coverage-is-rank-rounding
requires: []
---

Because `F_c` commutes with every marked-type projection
`Q_(c,lambda)`,

```text
R_(c,lambda)=F_c Q_(c,lambda)
```

is a projection.  For fixed `c` these projections are orthogonal as `lambda`
varies, and their sum is `F_cQ_c`.  Taking normalized matrix trace and then
summing over contexts gives exactly `(FWC4)`.

For each `R=R_(c,lambda)`, choose a subprojection `P<=R` of rank

```text
4 floor(rank(R)/4).
```

At most three matrix dimensions are discarded for each element of the fixed
finite menu `Omega`.  Hence

```text
sum_(c,lambda) tr_d(P_(c,lambda))
 >= E_forbid^mark-3|Omega|/d,
```

which is `(FWC5)`.

Every nonzero `P` now has dimension divisible by four.  Choose an orthonormal
basis of its range, split it into four equal pieces, and use the associated
matrix units.  The sum of two diagonal quarter-atoms is a projection `e<=P`
with `tr(e)=tr(P)/2`, while one quarter-atom is a projection `f<=P` with
`tr(f)=tr(P)/4`.  This proves `(FWC6)` and therefore the stated `GTC5` coverage
for the marked forbidden mass, with the explicit `3|Omega|/d=o(1)` loss.

Under `(FWC7)`, write the reducing type block as
`V_lambda tensor C^(m_lambda)` and trim only the multiplicity projection to
four-divisible rank.  The discarded ambient rank is then less than
`4 dim(V_lambda)` per marked type, giving `(FWC8)` after normalization and
summation over the fixed menu.