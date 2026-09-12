---
rg: 2
id: rank-density-from-approximate-rank-division
kind: claim
title: Uniform density of rank functions reduces to approximate division of rank functions by integers
distinct_from:
  rank-density-and-strict-comparison-give-purity: that turns rank density into purity under strict comparison; this reduces rank density itself to integer division of rank functions, with no comparison hypothesis.
  ah-algebras-realize-ranks-approximately: that proves rank density on AH algebras by realizing profiles directly at a stage; this shows that realizing arbitrary profiles is never needed, only dividing ranks of layer-cake elements.
artifacts:
  - research/artifacts/toms-winter-rank-density-firewall-2026-09-11.md
---

**Layer-cake bound.**  Let `A` be a unital C-star algebra with `T(A)`
nonempty, `a in A_+`, `K` an integer with `K >= ||a||`, and `L in N`.  Put

```text
b_L = direct_sum_(l=1..KL) (a - l/L)_+   in M_(KL)(A)_+.
```

Then for every trace `tau`,

```text
tau(a) - 1/L  <=  (1/L) d_tau(b_L)  <=  tau(a).
```

**Reduction.**  Let `A` be unital, simple, separable and exact with `T(A)`
nonempty.  Suppose ranks divide approximately: for every
`b in M_infty(A)_+`, `L in N` and `eta > 0` there is `y in M_infty(A)_+` with
`|L d_tau(y) - d_tau(b)| < eta` for all `tau`.  Then rank density holds: every
continuous strictly positive affine function on `T(A)` is a uniform limit of
rank functions.

So in any class, rank density, and with strict comparison purity, needs
only approximate division by integers of the rank functions of
functional-calculus elements.  It never needs realization of arbitrary
profiles.  The integer multiples `(1/L) d(b_L)` are free in every unital
algebra.
