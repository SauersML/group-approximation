---
rg: 2
id: fpbs-percolation-spine-path-bridge-ratio-criterion
kind: claim
title: On straight Z^2 paths with a supercritical percolation spine, Br/TJT equals the tilted gap density over r D_n and is pinched between c theta/D_n and 1/(r D_n), so the bridge bound lives or dies with exponential-scale coverage decorrelation D_n; numerically Br/TJT <= 0.5 on paths and two parallel routes for theta >= 0.45, bounded in n for each supercritical spine, and as the spine thins all growth runs through D_n
distinct_from:
  fpbs-annealed-pivotal-factorization-off-spine-bridges: that isolates the bridge mass Br and leaves open whether Br <= C(r) TJT over plain volumes; this computes Br and TJT exactly on path volumes for the percolation spine, proves the two-sided criterion, and measures the ratio on paths and two-route volumes
  fpbs-exhaustion-activation-gate-norm-law: that kills activation gates D^A <= kappa XJX by a norm law and its spark reduces Br <= C TJT to a covariance ratio with C(r) >= c/m(r) for grid spines; this identifies the covariance ratio on paths as D_n, shows the supercritical percolation spine is near the uncorrelated extreme (D_n at its geometric value), with D_n dropping only as the spine thins, and proves the ratio is at least of order theta/D_n for every path length
artifacts:
  - experiments/fpbs-percolation-spine-bridge-ratio-2026-09-17/brratio.c
  - experiments/fpbs-percolation-spine-bridge-ratio-2026-09-17/ana.py
  - experiments/fpbs-percolation-spine-bridge-ratio-2026-09-17/summarize.py
  - experiments/fpbs-percolation-spine-bridge-ratio-2026-09-17/run_all.sh
  - experiments/fpbs-percolation-spine-bridge-ratio-2026-09-17/run_big.sh
  - experiments/fpbs-percolation-spine-bridge-ratio-2026-09-17/results.txt
---

**Theorem 1 ESTABLISHED** (proof in
`fpbs-percolation-spine-path-bridge-ratio-criterion-proof`). **Numerics:
decisive computation in the accessible window.** **Scaling as `theta -> 0`:
OPEN**, with a heuristic prediction below.

**Setting.** This is the frame of
`fpbs-annealed-pivotal-factorization-off-spine-bridges` with a
label-independent environment `Z` that does not depend on `r`:
`omega_r = xi_r ∪ Z`. Given `Z`, an edge is open with probability `1` if it is
in `Z` and with probability `r` otherwise. `T = T^Lambda_r`, `J = J_W`, and
`Br = Br^Lambda_r` is the annealed mass of pivotals whose two separated
clusters both meet `V(Z ∩ Lambda)`.

The spine is the infinite cluster of Bernoulli(`p'`) bond percolation on `Z^2`
(`p' > 1/2`). Its edges are the open edges with an endpoint in the infinite
cluster. It is a factor of i.i.d., and its density `theta(p')` tends to `0`
as `p'` decreases to `1/2`.

The volume `Lambda` is the edge set of a chordless path
`u = x_0, ..., x_n = v`, with edges `e_k = x_{k-1} x_k`. Define:

* `N(i,j]` is the number of edges `e_{i+1}, ..., e_j` not in `Z`, and
  `t(i,j) = E r^{N(i,j]}`.
* `e_k` is an **interior gap** if `e_k notin Z` and there are `j < k < l`
  with `e_j, e_l in Z`. `G` is the number of interior gaps.
* `P*` is the law tilted by `r^N / E r^N`, with `N = N(0,n]`.
* The tilted gap density is `gamma_n = E*[G]/n`.
* The **coverage decorrelation** is `D_n = TJT(u,v) / (n T(u,v))`.

**Theorem 1.**

* (a) *Exact path formulas, for every environment.* `T(x_i,x_j) = t(i,j)`,
  `TJT(u,v) = sum_k [t(0,k-1) t(k,n) + t(0,k) t(k-1,n)]`,
  `Br(u,v) = E[G r^{N-1}]`. Hence
  ```text
  Br/TJT (u,v) = gamma_n / (r D_n),   gamma_n <= 1 - 2/n.
  ```
* (b) *Monotone i.i.d. factors.* If each `{e in Z}` is an increasing event
  of an i.i.d. field, then `t` is supermultiplicative along the path
  (Harris-FKG), and `D_n <= 1 + 1/t_1 <= 1 + 1/r`.
* (c) *Bypass lower bound.* For the percolation spine on a straight path in
  `Z^2`, and `2 <= k <= n-1`,
  `P*(e_k is an interior gap) >= r (1-p') p'^5 theta(p')`. Hence
  ```text
  (1-2/n)(1-p') p'^5 theta(p') / D_n  <=  Br/TJT  <=  1/(r D_n).
  ```

**Corollary 2 (the Br route on paths is a decorrelation statement).** Fix
`p'` and `r`. Then `sup_n Br/TJT < infinity` iff `inf_n D_n > 0`.

The ratio can grow like `1/theta` only through the covariance of the
coverage: that requires `D_n <= theta/(rK)` for a ratio `K/theta`. Gap
counting, pivotality and bridging cost only bounded factors: `gamma_n` lies
between `r(1-p')p'^5 theta (1-2/n)` and `1`.

If the coverage were exactly independent at the exponential scale
(`t(i,j) = lambda^{j-i}`), then `D_n = lambda + 1/lambda` for every `n`.

The opposite extreme is all-or-nothing coverage: `Z ∩ Lambda` is either
everything (probability `m`) or nothing. Then `t(i,j) = m + (1-m) r^{j-i}`
and `D_n -> m`. In this pure form `Br = 0`, because there are no gaps. Adding
sparse gaps to such coverage gives the `C(r) >= c/m(r)` covariance mechanism
of the spark of `fpbs-exhaustion-activation-gate-norm-law`.

## Why crude bounds cannot decide the `theta -> 0` scaling

Here `t_l = t(0,l)` for a straight path. There are two rigorous bounds:

* **Upper bound.** `{A ⊆ Z}` implies that `A` is open and that the
  `l`-box meets infinity off the segment, and these two events are
  independent. This gives `t_l <= r^l + (r+p')^l q_l`, with
  `q_l <= (l+1) theta`.
* **Lower bound.** Supermultiplicativity and Fekete give `t_l <= lambda^l`
  with `lambda = sup_l t_l^{1/l}`. Also `t_l >= max(r^l, p'^l theta)`
  (FKG), so `max(r, p') <= lambda <= r + p'`.

Nothing forces the exponential rates of these bounds to match. So they cannot
locate `g(l) = t_l / lambda^l`, the *attachment factor*, which alone decides
`D_n`. On paths, the Br route is a statement about the attachment profile of
the `r^N`-tilted near-critical cluster. Gap counting, pivotality and
bridging do not decide it.

**Heuristic (OPEN, not used anywhere).** Suppose `g(l) ≈ (r/lambda)^l +
c theta l^beta` for `1 << l << xi(p')`, with `beta = 5/48` the one-arm
exponent. This is quasi-multiplicativity of one-arm events for the tilted
measure: a covered stretch of length `l` attaches to infinity with
probability about `pi(xi)/pi(l)`. Then

```text
D_n ≈ (C_b + c theta n^{1+beta}) / n,
Br/TJT ≈ n / (C_b + c theta n^{1+beta}),
sup_n Br/TJT ≍ theta^{-1/(1+beta)} = theta^{-48/53},
```

and the supremum is attained at `n ≍ theta^{-48/53}`, far below `xi`. For
`n >> xi` the attachment saturates, `D_n` returns to order `1`, and the ratio
is bounded. So the prediction for the percolation spine is growth
**slower than `1/theta`**, visible only below the correlation length.

## Computation (decisive in the accessible window)

**Method.** `brratio.c` works in a box with margin `M` around the volume, and
takes the spine to be the clusters that touch the box boundary. The
environment off `Lambda` is sampled once per environment and compressed by
union-find. The `Lambda` edges are then resampled `K` times, with importance
sampling: the proposal opens them with probability `p'/a`,
`a = p' + (1-p') r`. Each resample yields `T(u,x)` and `T(x,v)` for all
`x in W`, `T(u,v)`, `Br` (exact quenched pivotal/bridge enumeration), the
histogram of `N`, and the untilted spine density `theta` at the middle
vertex. `ana.py` forms `TJT`, the ratio, `D_n`, `gamma_n` and
`K2 = T(0,n)/(T(0,n/2) T(n/2,n))`, with jackknife errors over batches.

Calibration:

* With `M = 0` (spine = open edges, i.i.d.) the Monte Carlo matches exact
  enumeration: `Br` 0.4471 against 0.44744 on the path `n = 8`; `T(u,v)`,
  `Br`, `TJT` on a `3 x 2` rectangle.
* At `p' = 0.55`, `n = 32`, margins `M = 50` and `M = 150` agree.

Commands: `gcc -O2 -o brratio brratio.c -lm; sh run_all.sh ./brratio runs;
sh run_big.sh ./brratio runs; python3 summarize.py runs`. The full table is
`results.txt`.

**Supercritical spines** (`M >> xi`, `n = 1..256`). `Dg = lambda + 1/lambda`
with `lambda = T(0,n)/T(0,n-1)` is the value of `D` for exactly geometric
`t`.

| `p'` | `theta` proxy | `Br/TJT` at `n=256`, `r=0.3` / `0.6` | `D_32/Dg` (`r=0.3`) |
|---|---|---|---|
| 0.85 | 1.00 | 0.083 / 0.079 | 1.00 |
| 0.7 | 0.99 | 0.183 / 0.167 | 1.00 |
| 0.6 | 0.95 | 0.259 / 0.236 | 0.99 |
| 0.55 | 0.90 | 0.303 / 0.268 | 0.98 |
| 0.52 | 0.79 | 0.341 / 0.293 | 0.94 |

The ratio increases with `n` and plateaus by `n ≈ 64` for every `p'`, so it
is bounded. `K2` stays within `1.00-1.08`. The growth as `p'` falls comes
from `gamma` (0.05 to 0.21 at `r = 0.3`): more closed edges mean more gaps.
`D` stays at its geometric value.

**Critical proxies** (`p' = 1/2`, spine = clusters reaching distance `M`).
The density falls like `M^{-5/48}`.

| `M` | `theta` proxy | `Br/TJT` at `n=128`, `r=0.3` / `0.6` | `gamma_128` (`r=0.3`) | `D_32/Dg` (`r=0.3` / `0.6`) |
|---|---|---|---|---|
| 10 | 0.73 | 0.360 / 0.309 | 0.210 | 0.92 / 0.96 |
| 40 | 0.65 | 0.374 / 0.329 | 0.197 | 0.81 / 0.88 |
| 160 | 0.56 | 0.438 / 0.385 | 0.213 | 0.70 / 0.81 |
| 640 | 0.49 | 0.491 / 0.421 | 0.206 | 0.63 / 0.70 |
| 2560 | 0.43 | 0.516 ± 0.038 / — | 0.180 | 0.60 / — |

The `M = 2560` row uses 150 environments at `r = 0.3` only, for
`n in {8, 32, 128}`. The measured density is `0.44 ± 0.04`, which matches
`0.49 · 4^{-5/48} ≈ 0.43`.

As the spine thins, `gamma` is flat (0.20 ± 0.01). `D_n` falls below the
geometric value, and `K2` rises to 1.5-1.7. So all of the growth of the ratio
goes through the covariance term `D_n`, as Corollary 2 says it must. The
effective exponent of the ratio in `1/theta` over this window is
`0.77 ± 0.11` (`r = 0.3`, weighted fit over all five rows) and about `0.7`
(`r = 0.6`). This is consistent with the heuristic `48/53 ≈ 0.91`. It is
also compatible with `1`, at 2 sigma.

**Two parallel routes** (the boundary of an `n x h` rectangle; `u`, `v` are
the bottom corners). For `n in {8,32,128}` and `h in {2,8,32}`, the ratio
does not depend on `h` within errors, and it equals the single-path ratio of
the same `n` and spine:

* 0.297 against 0.297 at `p' = 0.55`;
* 0.18 against 0.181 at `p' = 0.7`;
* 0.43-0.47 against 0.44 for the `M = 160` proxy.

The second route adds no bridging mechanism beyond the path criterion.

**What this rules out.** In the whole accessible window
(`theta >= 0.45`, `r in {0.3, 0.6}`, paths of length up to `256`, and
two-route volumes), `Br <= C TJT` holds with `C = 0.5`. At `theta ≈ 0.43`
(`M = 2560`) the ratio is already `0.52 ± 0.04`, so the best constant keeps
rising as the spine thins. For each fixed
supercritical spine it holds uniformly in `n`.

So there is no bridge-driven failure of the Br route at bounded density. The
only possible failure is `theta -> 0` growth through `D_n`. It is measured
at rate at most about `theta^{-0.8}` here. On the path class it is reduced
exactly to the attachment profile `g(l)` of the tilted cluster.

## Consequence for the Br route

Take a spine family born from nothing, `m(r) -> 0` (the setting of
`fpbs-exhaustion-activation-gate-norm-law`). A percolation-type spine then
forces `C(r) >= c/D_{n(r)}(r) · theta`. If the heuristic holds, this
diverges like `m(r)^{-48/53}`, not like `1/m(r)`.

So the Br route cannot use a constant `C(r)` bounded at the spine birth.
Any usable form must tolerate `C(r) ~ m(r)^{-kappa}`. Here `kappa = 48/53`
is conjectural. `kappa <= 1` would follow from `D_n >= c theta`, which is not
proved.

**Next step.** Prove the one-sided attachment bound
`g(n) <= C theta^{-1} g(k) g(n-k)` for a positive fraction of `k`, which
gives `D_n >= c theta`. It is a quasi-multiplicativity statement
for the `r^N`-tilted cluster. It would give `Br/TJT <= C'/theta` on all path
volumes, and hence a rigorous `kappa <= 1`.
