---
rg: 2
id: hs-per-atom-compressor-clause-is-vacuous-proof
kind: route
title: Bound small projections by their own trace and count collisions of the mass-weighted clause
target: hs-per-atom-compressor-clause-is-vacuous
requires: []
artifacts:
  - c1168433:official/counterexample.tex
---

Write `t_j = tau(p_j)`, `y_j = W p_j W^*`, and note `||P||_2 = tau(P)^(1/2)`
for a projection `P`.

**Item 1.**  `||y_j - p_j||_2 <= ||y_j||_2 + ||p_j||_2 = 2 t_j^(1/2) <= eps`
when `t_j <= eps^2/4`, and `tau(p_j) >= tau(p_j) - eps`.

**Item 2.**  If `t_j, t_k <= eps^2/4` then
`||y_j - p_k||_2 <= t_j^(1/2) + t_k^(1/2) <= eps` and
`t_k >= 0 >= t_j - eps`.  The ratio `t_k/t_j` is unconstrained.

**Failure of `(6)`.**  By item 2, on the atoms of trace at most `eps^2/4` the
clause is satisfied by every matching, including ones sending every atom to
an atom of arbitrarily smaller trace.  The one-sided size drift the median
step needs is a statement about exactly these ratios, so it is not a
consequence of `(PA)` on that mass.

**`(MW)` implies `(6)`.**  Put `e_j = ||y_j - p_(sigma(j))||_2^2`, so
`sum_j e_j <= eps`.

*Collisions.*  If `sigma(j)=sigma(k)=m` with `j != k`, then `y_j y_k = 0`, so

```text
t_j + t_k = ||y_j - y_k||_2^2 <= (e_j^(1/2) + e_k^(1/2))^2 <= 2(e_j + e_k).
```

In a collision class `S_m` with at least two atoms, pick `k*` minimizing `e`.
Every `j != k*` has `t_j <= 2(e_j + e_(k*)) <= 4 e_j`, and `t_(k*) <= 4 e_(j')`
for any other `j'`.  Hence `sum_(j in S_m) t_j <= 8 sum_(j in S_m) e_j`, and
the colliding atoms carry total trace at most `8 eps`.  Off them `sigma` is
injective and its images are pairwise orthogonal.

*Ratios.*  For a difference of projections `x = y_j - p_(sigma(j))`,
`|t_j - t_(sigma(j))| = |tau(x)| <= ||x||_1 <= ||x||_2 tau(s)^(1/2)` with `s`
the support of `x`, `tau(s) <= t_j + t_(sigma(j))`.  So

```text
|t_j - t_(sigma(j))| <= (e_j (t_j + t_(sigma(j))))^(1/2).
```

Call `j` good if `e_j <= eps^(1/2) t_j`.  Bad atoms satisfy
`t_j < eps^(-1/2) e_j`, so they carry trace at most `eps^(1/2)`.  On a good
atom with `rho = t_(sigma(j))/t_j`, the display gives
`|1 - rho| <= eps^(1/4) (1 + rho)^(1/2)`, which forces `rho >= 1 - 2 eps^(1/4)`
once `eps^(1/4) <= 1/2` (if `rho <= 3` the right side is at most
`2 eps^(1/4)`; if `rho > 3` there is nothing to prove).

Outside total trace `8 eps + eps^(1/2)` the matching is therefore injective
and multiplicatively non-shrinking with loss `2 eps^(1/4)`, which is `(6)`
with `eta = 2 eps^(1/4)`, exactly as `(5)`--`(6)` are used in Step 2 of the
permutation proof (`official/counterexample.tex`).
