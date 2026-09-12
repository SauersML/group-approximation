---
rg: 2
id: stw27-coordinate-euler-slack-obstructs-compact-dividers
kind: claim
title: Coordinate Euler mass defeats the plus-one slack for compact Villadsen dividers
distinct_from:
  hopf-power-blocks-obey-weighted-hall-euler-criterion: that claim characterizes nonvanishing Euler classes for sums of prescribed Hopf-power blocks; this claim uses mod-prime total Chern classes to obstruct an almost-divisibility sandwich by an arbitrary vector bundle.
artifacts:
  - research/artifacts/stw27-villadsen-compact-divider-no-go-audit-2026-08-30.md
  - research/artifacts/stw27-soft-divider-hinge-audit-2026-08-30.md
---

Let `ell` be prime and let `L_1,...,L_N` be the coordinate Hopf line
bundles on `(S^2)^N`.  Fix positive integers `t_1,...,t_N` and `s>=0`,
and put

```text
E = theta_s direct_sum direct_sum_(i=1)^N L_i^(direct_sum t_i),
M = rank(E)=s+sum_i t_i,
N_ell = cardinality {i : ell does not divide t_i}.
```

If a vector bundle `F` satisfies

```text
ell F is a subbundle of E,
E is a subbundle of (ell+1)F,
```

then necessarily

```text
(ell+1)N_ell <= M.                                    (V)
```

In particular, if all coordinate eigenmaps are multiplicity-free, so that
`t_i=1`, the existence of a compact `ell`-almost divider forces

```text
N/M <= 1/(ell+1).
```

The obstruction persists in a simple injective diagonal Villadsen type-I
limit with seed `S^2`.  Let `q` be the seed Hopf projection and let `x` be
its limit class.  For the map from the seed to stage `j`, let `M_j` be the
total eigenmap multiplicity and let `N_(ell,j)` count coordinate projections
whose multiplicities are nonzero modulo `ell`.  If

```text
(ell+1)N_(ell,j) > M_j
```

eventually, then no compact element `y in Cu(A)` satisfies

```text
ell y <= x <= (ell+1)y.                                (C)
```

Consequently, if such a Villadsen limit is almost divisible, every witness
for `(C)` must be genuinely noncompact.  Numerical or even factorial
divisibility of the total matrix multiplicities does not produce a compact
divider while the coordinate Euler mass remains above the threshold.

For a single homogeneous block of rank `M<ell(ell+1)`, there is no soft
loophole: `stw27-low-rank-soft-divider-rounding` shows that every alleged
`(ell,ell+1)`-divider is automatically compact.  This bound cannot persist
for the image of a fixed projection along an infinite Villadsen tail because
its rank grows without bound.
