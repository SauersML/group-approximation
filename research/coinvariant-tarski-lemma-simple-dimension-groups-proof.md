---
rg: 2
id: coinvariant-tarski-lemma-simple-dimension-groups-proof
kind: route
title: Refine the paradoxical decomposition of Nx into N columns, divide every piece by N using density, and move all pieces at once
target: coinvariant-tarski-lemma-simple-dimension-groups
requires: []
---

**One-step moves form a congruence.**  The relation `~` is reflexive, symmetric
(use `t_i^(-1)`) and additive.  Transitivity uses (R) (Rainone, Lemma 4.7):
from `y = sum c_i`, `sum alpha_(t_i) c_i = sum d_j` and `y'' = sum alpha_(r_j) d_j`,
refine `alpha_(t_i) c_i = sum_j f_ij`, `d_j = sum_i f_ij`.  Then
`y = sum_ij alpha_(t_i)^(-1) f_ij` and
`y'' = sum_ij alpha_(r_j t_i)(alpha_(t_i)^(-1) f_ij)`.  If `[y] = 0`, then
`y = 0`: the pieces `c_i` satisfy `sum alpha_(t_i) c_i = 0`, so every
`c_i = 0` by (R).

**Division.**  Suppose `N[x] = N[x] + [e]` with `e != 0`, i.e.
`Nx = sum_(i<=m) c_i` and `Nx + e = sum_i alpha_(t_i)(c_i)`.  Refine
`sum_i c_i = x + ... + x` (`N` terms): `c_i = sum_(j<=N) c_ij` with
`sum_i c_ij = x` for each `j`.  By (U), `e^ >= eta > 0` on `S` for some `eta`.
Put `L = max_i sup_(s in S) s(alpha_(t_i) x_0)`, which is finite.  Each
positive functional `s o alpha_(t_i)` equals `lambda s'` with `s' in S` and
`0 <= lambda <= L`.  Choose `epsilon > 0` with `m N^2 (L + 1) epsilon < eta/2`.
For each `c_ij != 0` we have `mu_ij = min_S c_ij^ > 0` by (U).  By (D) pick
`d_ij in G` with `d_ij^` within `min(epsilon/4, mu_ij/(8N))` of
`c_ij^/N - min(epsilon/2, mu_ij/(4N))`.  Then on `S`

```text
0 < d_ij^,     N d_ij^ < c_ij^,     c_ij^ - N d_ij^ < N epsilon,
```

so `d_ij > 0` and `c_ij - N d_ij > 0` by (O).  Put `d_ij = 0` if `c_ij = 0`.

**The move.**  Let `y = sum_ij d_ij`.  Since
`N(x - y) = sum_ij (c_ij - N d_ij)` is strictly positive on `S` (every term is
nonnegative and at least one is positive, because `x != 0`), (O) gives
`r = x - y in G^+`.  One move gives

```text
x = y + r  ~  x' := sum_ij alpha_(t_i)(d_ij) + r.
```

For `s in S`, using `sum_ij [s(alpha_(t_i) c_ij) - s(c_ij)] = s(Nx + e) - s(Nx) = s(e)`,

```text
N s(x' - x) = sum_ij [ s(alpha_(t_i)(N d_ij)) - s(N d_ij) ]
            = s(e) - sum_ij [ s(alpha_(t_i)(c_ij - N d_ij)) - s(c_ij - N d_ij) ].
```

The error term has absolute value at most `m N (L + 1) N epsilon < eta/2`, so
`s(x' - x) > 0` for all `s`.  By (O), `e' = x' - x in G^+ \ {0}`, and
`[x] = [x] + [e']` is infinite.

**Proper infiniteness.**  By (U) every nonzero `[y]` is an order unit of
`Sigma`.  In a simple conical monoid an infinite element is properly infinite:
`[x] = [x] + k[e']` for all `k`, and `[x] <= k[e']` for some `k`, so
`2[x] <= [x] + k[e'] = [x]`.  Finally, `(k+1) theta <= k theta` means
`k theta = (k+1) theta + t = k theta + (theta + t)` with `theta + t != 0`, so
`k theta` is infinite and `theta` is properly infinite by the above.
