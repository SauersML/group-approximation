---
rg: 2
id: fpbs-hairpin-paths-break-uniform-bridge-ratio
kind: claim
title: Folded paths break the plain-volume bridge ratio; in a connected Z^2-invariant range-1 monotone factor of iid with full density, hairpin paths have Br/TJT growing linearly in n and coverage decorrelation K exponential in n, while straight paths in the same environment stay bounded with K = 1; linear is the maximal order in every environment, and for every finite-range monotone environment the fold width alone bounds Br/TJT and K on paths
distinct_from:
  fpbs-percolation-spine-path-bridge-ratio-criterion: that proves the path formulas and measures Br/TJT on straight paths, where it is bounded; this shows that the same formulas on a folded chordless path give Br/TJT of order n in a connected invariant environment of density 1, so no bound over plain volumes can be uniform in the path
  fpbs-annealed-pivotal-factorization-off-spine-bridges: that leaves open whether Br <= C(r) TJT over plain volumes; this answers it negatively for connected label-independent environments at every r, by an exact closed form
artifacts:
  - experiments/fpbs-hairpin-bridge-ratio-2026-09-18/exact_column.py
  - experiments/fpbs-hairpin-bridge-ratio-2026-09-18/exact_column.txt
  - experiments/fpbs-hairpin-bridge-ratio-2026-09-18/hairpin.c
  - experiments/fpbs-hairpin-bridge-ratio-2026-09-18/kpattern.c
  - experiments/fpbs-hairpin-bridge-ratio-2026-09-18/run_all.sh
  - experiments/fpbs-hairpin-bridge-ratio-2026-09-18/results.txt
---

**ESTABLISHED (class-killing obstruction plus strict reduction): Theorems
1-3 and Corollary 4.** Proof in
`fpbs-hairpin-paths-break-uniform-bridge-ratio-proof`. **The
percolation-spine case: OPEN**, with Monte Carlo evidence that the same fold
mechanism is present at a much smaller rate (Conjecture 5).

**Setting.** As in `fpbs-percolation-spine-path-bridge-ratio-criterion`: a
label-independent environment `Z` that does not depend on `r`,
`omega_r = xi_r ∪ Z`, and a chordless path `x_0 ... x_n` in `Z^2` with edges
`e_k = x_{k-1} x_k`, used as the volume `Lambda`. `N(i,j]` is the number of
edges `e_{i+1},...,e_j` not in `Z`, `t(i,j) = E r^{N(i,j]}`, `T = t(0,n)`,
and by Theorem 1(a) there

```text
TJT = sum_k [ t(0,k-1) t(k,n) + t(0,k) t(k-1,n) ],   Br = E[G r^{N-1}],
Br/TJT = gamma_n / (r D_n),   D_n = TJT/(n T),   gamma_n = E*[G]/n,
```

where `G` counts interior gaps and `P*` is the `r^N`-tilted law. The
coverage decorrelation constant `K_n(Z)` is the maximum, over split edges
`e_k` and patterns `S ⊆ Lambda \ {e_k}` with parts `S^-` before and `S^+`
after `e_k`, of `P(S ⊆ Z) / (P(S^- ⊆ Z) P(S^+ ⊆ Z))`. It bounds `Br/TJT`
for every environment (Theorem 1 of the coverage-decorrelation node of
w10-123, `fpbs-path-bridge-ratio-untilted-coverage-decorrelation`, in the
land queue at the time of writing).

**Theorem 1 (linear is the maximal order).** For every environment, every
`r in (0,1)` and every chordless path,

```text
n D_n = sum_k ( t(0,k-1) t(k,n) + t(0,k) t(k-1,n) ) / t(0,n) >= 2,
Br/TJT <= (n-2) / (2r).
```

The `k = 1` and `k = n` terms are at least `1`, because `N` only drops when
edges are removed. `G <= n-2` gives the rest.

**The column environment.** Let `zeta_{j,y}`, `(j,y) in Z^2`, be i.i.d.
Bernoulli(`q`), `q in (0,1)`, and put `u = 1-q`. Write `h(j,y)` for the
horizontal edge `(j-1,y)(j,y)`. Let `Z` consist of

* every vertical edge of `Z^2`, and
* every horizontal edge `h(j,y)` with
  `max(zeta_{j,y-1}, zeta_{j,y}, zeta_{j,y+1}) = 1`.

`Z` is a monotone factor of i.i.d. of range `1`, invariant under all
translations of `Z^2`. The graph `(V(Z), Z)` is connected a.s., and
`V(Z) = Z^2`, so the spine density is `theta = 1`. As a constant family in
`r` it is a connected label-independent environment in the sense of
`fpbs-annealed-pivotal-factorization-off-spine-bridges`.

**The hairpin.** For `m >= 1`, `H_m` is the path
`(0,0),(1,0),...,(m,0),(m,1),(m,2),(m-1,2),...,(0,2)`, with `n = 2m+2`
edges. Its arms are `a_j = h(j,0)` and `b_j = h(j,2)`, and its two turn
edges are vertical. It is chordless, since the arms are at vertical
distance `2`. The arm edges `a_j` and `b_j` in the same column share the
seed `zeta_{j,1}`, and that is the whole mechanism.

Put

```text
lambda = 1 - (1-r) u^3,
mu     = lambda^2 + (1-r)^2 u^5 (1-u),     rho = mu / lambda^2 > 1,
alpha  = ( r^2 u^5 + r (u^3 - u^5) ) / mu,
A      = 2 (lambda^{-1} + lambda rho) / (rho - 1),
kappa  = (1 - 2u^3 + u^5) / (1 - u^3)^2 = 1 + u^5 (1-u)/(1-u^3)^2 > 1.
```

**Theorem 2 (exact hairpin formulas).** In the column environment, for
every `q, r in (0,1)` and `m >= 1`:

* (a) `t(I) = lambda^{a(I)} rho^{c(I)}` for every interval `I` of `H_m`,
  where `a(I)` is the number of arm edges in `I` and `c(I)` is the number of
  columns `j` with both `a_j` and `b_j` in `I`.
* (b) The coverage decorrelation is summable:
  ```text
  n D_n = 2 sum_{j=1}^m ( lambda^{-1} rho^{-j} + lambda rho^{1-j} ) + 4 rho^{-m}
        <= A + 4.
  ```
* (c) Under `P*` the columns stay i.i.d., `P*(a_j notin Z) = alpha`, and
  ```text
  E*[G] = 2 m alpha - 2 alpha (1 - alpha^m)/(1 - alpha).
  ```
* (d) Hence
  ```text
  Br/TJT (H_m)  >=  alpha ( n - 2 - 2/(1-alpha) ) / ( r (A + 4) ),
  ```
  which grows linearly in `n`, with slope `alpha/(r A)` in the limit.
* (e) Split at the first turn edge, with `S^- = {a_1,...,a_m}` and
  `S^+ = {b_1,...,b_m}` (one run on each side). Then
  `P(S ⊆ Z) / (P(S^-⊆Z) P(S^+⊆Z)) = kappa^m`, so
  `K_n(Z) >= kappa^{(n-2)/2}`.
* (f) *Straight paths, same environment.* On a horizontal path of `n` edges,
  `t(i,j) = lambda^{j-i}`, `D_n = lambda + 1/lambda`,
  `Br/TJT <= 1/(r(lambda + 1/lambda)) < 1/(2r)`, and `K_n(Z) = 1`. On a
  vertical path every edge is covered and `Br = 0`.

**Theorem 3 (fold width controls paths in finite-range environments).**
Let `Z` be an increasing factor of an i.i.d. field `(zeta_v)` of range `R`:
`{e in Z}` is an increasing function of the seeds within graph distance `R`
of an endpoint of `e`. For edges `e, e'` let `d(e,e')` be the least distance
between their endpoints. The **fold width** `w_R` of a chordless path is the
least `w >= 0` with `d(e_i, e_j) > 2R` whenever `j - i >= 2w + 2`. Put
`lambda_min = min_k E r^{1{e_k notin Z}} >= r` and
`pi_+ = min { P(e_k in Z) : P(e_k in Z) > 0 }`. Then

```text
D_n >= lambda_min^{2 w_R},     Br/TJT <= 1 / (r lambda_min^{2 w_R}),
K_n(Z) <= pi_+^{-2 w_R}.
```

Every geodesic lattice path in `Z^d` has `w_R <= R`. So in finite-range
monotone environments the bridge ratio and `K` are bounded on geodesic
paths, uniformly in `n` and in the pattern. The hairpin `H_m` has fold width
of order `m`, and Theorem 2 shows that exponential dependence on the fold
width is attained by `K`.

**Corollary 4 (what dies, what survives).**

* **Dead:** `Br^Lambda_r <= C(r) T J T` uniformly over plain volumes, for
  connected label-independent environments, at every `r in (0,1)`, already
  for a translation-invariant, range-1, monotone factor of i.i.d. with spine
  density `1` (Theorem 2(d)). A uniform bound over plain volumes has to use
  more of the environment than connectivity, invariance, finite range,
  monotonicity and density.
* **Dead:** any proof of the multi-run bound `K_n(Z) <= C/theta` that holds
  over all chordless paths and uses only those properties. In the column
  environment `K_n >= kappa^{(n-2)/2}` with `theta = 1`, already for one run
  on each side (Theorem 2(e)). The two-run bound `K <= 2/theta_min` of the
  coverage-decorrelation node uses the last-exit decomposition of Bernoulli
  percolation, which the column environment does not have. A proof of the
  multi-run bound for the percolation spine must therefore either use
  percolation structure throughout or use path geometry.
* **Dead:** lower bounds on `D_n` from Harris-FKG supermultiplicativity
  alone. The column environment is a monotone factor of i.i.d., and on
  `H_m` it has `D_n <= (A+4)/n -> 0`.
* **Survives:** the Br route on unfolded volumes. For finite-range monotone
  environments, Theorem 3 closes it on geodesic paths with an explicit
  constant. The gate of `fpbs-annealed-pivotal-factorization-off-spine-bridges`
  uses only one exhaustion. In the box volume `[0,w] x [0,h]` the column
  environment restricted to the box is connected outside an event of
  probability at most `w u^{h+1}` (adjacent vertical segments are joined as
  soon as one of their `h+1` seeds is `1`), and `Br` vanishes when
  `Z ∩ Lambda` is connected. So this environment puts bridge mass only on an
  exponentially rare event along box exhaustions. The fold obstruction lives
  in thin folded volumes.

**Conjecture 5 (the percolation spine also folds; OPEN).** For the Z^2
supercritical percolation spine, `log t(0,n) - 2 log t(0,n/2)` on `H_m`
grows linearly in `m`, at a positive rate `s(p', r)`. Likewise `log K`
grows linearly in the number of matched run pairs `(a_{2i-1}, b_{2i-1})`.
Suppose, more generally, that a split at `a_c` or `b_c` costs a factor about
`e^{-s c}`, as it does exactly (with `e^s = rho`) in the column environment.
Then `n D_n` stays bounded on hairpins, of order `4/s`, and `Br/TJT(H_m)`
grows linearly once `n >> 1/s`. The rate is small: `s ≈ 0.0024` per column
at `p' = 0.55`, `r = 0.5`. So the linear regime would start only at `n` of
order a thousand.

## Computation

**Exact, column environment** (`exact_column.py`, output
`exact_column.txt`). A transfer computation over columns gives `T`, `TJT`,
`Br` and `alpha` on `H_m` for `m` up to `199`. It matches brute-force
enumeration over all environments for `m <= 4` to 12 digits, and the closed
forms of Theorem 2 to all printed digits. The closed forms then give
`n` up to `200000`. Selected rows (`H` = hairpin, `S` = straight path of the
same length):

| `q` | `r` | `n` | `n D_n (H)` | `Br/TJT (H)` | `Br/TJT (S)` |
|---|---|---|---|---|---|
| 0.1 | 0.1 | 400 | 16.77 | 28.07 | 0.648 |
| 0.1 | 0.1 | 200000 | 16.77 | 14185.9 | (bounded) |
| 0.1 | 0.9 | 400 | 749.6 | 0.407 | 0.385 |
| 0.1 | 0.9 | 200000 | 5840.9 | 26.67 | (bounded) |
| 0.5 | 0.6 | 400 | 615.2 | 0.080 | 0.065 |
| 0.5 | 0.6 | 200000 | 1447.8 | 17.17 | (bounded) |
| 0.5 | 0.9 | 200000 | 24967.9 | 1.001 | (bounded) |

For small `n` the hairpin and the straight path are indistinguishable. The
linear regime starts at `n ≈ A`, which is large when `rho` is close to `1`
(`r` near `1`, or `q` large).

**Monte Carlo, percolation spine** (`hairpin.c`, `kpattern.c`; box proxy
with margin `L = 12`: the spine is the open edges whose cluster meets the
box boundary; importance sampling on the path edges; errors from 10 batch
means). At `p' = 0.55`, `r = 0.5`, 40000 samples:

| `n` | `Lmid (H)` | `Lmid (S)` |
|---|---|---|
| 22 | 0.0397 ± 0.0035 | 0.0142 ± 0.0030 |
| 42 | 0.0657 ± 0.0039 | 0.0118 ± 0.0040 |
| 82 | 0.1133 ± 0.0055 | 0.0197 ± 0.0048 |
| 162 | 0.2066 ± 0.0062 | -0.0007 ± 0.0061 |

The hairpin excess is linear in `m = (n-2)/2`, with slope `0.00235` per
column from `m = 20` to `m = 80`. The straight excess is flat. Matched
multi-run patterns (`l` single-edge runs per side, at `p' = 0.55`) give

| `l` | `log K (H)` | `log K (S)` |
|---|---|---|
| 2 | 0.0266 ± 0.0044 | 0.0036 ± 0.0033 |
| 4 | 0.0440 ± 0.0036 | 0.0025 ± 0.0037 |
| 8 | 0.0683 ± 0.0089 | -0.0018 ± 0.0039 |
| 16 | 0.1381 ± 0.0098 | 0.0067 ± 0.0080 |

This is linear in `l` on the hairpin and flat on the straight path. At
`n = 30`, `p' = 0.55`, `r = 0.2`, the direct ratio is still the same on both
paths (hairpin `Br/TJT = 0.2955 ± 0.0010`, `n D_n = 63.95`; straight
`0.2925 ± 0.0013`, `64.74`), as the small rate predicts. Caveat: with a
fixed margin, the box proxy is not the infinite cluster, so the numerics
support Conjecture 5 but do not decide it.

Reproduction: `sh run_all.sh` (single-threaded, fixed seeds; each command
is under 20 minutes). The raw lines are in `results.txt`. Further rows there
(`n = 22` at `p' = 0.6, 0.7`) show the excess shrinking as the spine
thickens, as in the column environment when `q` grows.
