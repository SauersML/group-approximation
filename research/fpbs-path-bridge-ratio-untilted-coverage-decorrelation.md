---
rg: 2
id: fpbs-path-bridge-ratio-untilted-coverage-decorrelation
kind: claim
title: On chordless paths Br/TJT is at most the untilted coverage decorrelation constant K = max P(S in Z)/(P(S^- in Z)P(S^+ in Z)), the r^N tilt cancels; for percolation spines on any graph a last-exit union bound gives K <= 2/theta on two-run patterns, hence g(n) <= 2 theta^-1 g(k)g(n-k) for every k and Br/TJT <= 2/theta as r -> 0 uniformly in n; multi-run K open, measured K theta <= 0.93 down to theta 0.48
distinct_from:
  fpbs-percolation-spine-path-bridge-ratio-criterion: that writes Br/TJT = gamma_n/(r D_n) through the r^N-tilted law and leaves the tilted attachment quasi-multiplicativity open; this removes the tilt by a subset expansion, bounds Br/TJT directly by an untilted coverage ratio over patterns, and proves the one-arm quasi-multiplicativity g(n) <= 2 theta^-1 g(k) g(n-k) for every k on every graph
artifacts:
  - experiments/fpbs-coverage-decorrelation-2026-09-18/kdecor.c
  - experiments/fpbs-coverage-decorrelation-2026-09-18/run_all.sh
  - experiments/fpbs-coverage-decorrelation-2026-09-18/results.txt
---

**Theorems 1, 2 and Corollary 3 ESTABLISHED** (proof in
`fpbs-path-bridge-ratio-untilted-coverage-decorrelation-proof`).
**Multi-run bound: OPEN**, with a decisive computation in the accessible
window.

**Setting.** As in `fpbs-percolation-spine-path-bridge-ratio-criterion`: a
chordless path `x_0 ... x_n` with edges `e_i`, a label-independent
environment `Z`, `omega_r = xi_r ∪ Z`, `t(i,j) = E r^{N(i,j]}`, and `Br`,
`TJT`, `D_n` as there. For `2 <= k <= n-1` put `I_k = Lambda \ {e_k}`. For
`S ⊆ I_k`, `S^-` is the part of `S` before `e_k` and `S^+` the part after it.
The **coverage decorrelation constant** is

```text
K_n(Z) = max_{2<=k<=n-1}  max_{S ⊆ I_k, P(S ⊆ Z) > 0}  P(S ⊆ Z) / ( P(S^- ⊆ Z) P(S^+ ⊆ Z) ).
```

It does not involve `r`.

**Theorem 1 (the tilt cancels).** For every environment, every `r in (0,1)`
and every `n`,

```text
Br(u,v) / TJT(u,v) <= K_n(Z),        D_n >= (1 - 2/n) / K_n(Z).
```

*Mechanism.* Expand
`r^{#(I\Z)} = sum_{S ⊆ I} r^{|I|-|S|}(1-r)^{|S|} 1{S ⊆ Z}`. The bridge
mass is `sum_k E[1{e_k gap} r^{N-1}]`, and it expands over `S ⊆ I_k` into
terms of at most `P(S ⊆ Z)`. The gap-split part `t(0,k-1) t(k,n)` of `TJT`
expands over the same `S` with the same weights, with terms
`P(S^- ⊆ Z) P(S^+ ⊆ Z)`. The mediant inequality then gives the bound.

So the tilted quasi-multiplicativity asked for by the criterion is implied by
an **untilted** statement about the environment alone: the coverage events
`{S ⊆ Z}` split across one missing edge at a bounded cost, uniformly over
patterns `S`. The tilted law, the gap density `gamma_n` and pivotality no
longer appear.

**Theorem 2 (two-run patterns, every graph).** Let `omega` be Bernoulli(`p'`)
bond percolation on any locally finite graph and `T` any target: a vertex
set, or "infinity". Let `Z` be the open edges with an endpoint joined to
`T`, and put `theta_min = min_i P(x_i <-> T)`. Let `q(F)` be the probability
that every run of `F` is joined to `T` when `F` is declared open, so that
`P(F ⊆ Z) = p'^{|F|} q(F)`.

For two runs `L` before `R`, taking the last exit of a path to `T` from
`V(L ∪ R)` gives

```text
q(L ∪ R) <= q(L) + q(R) <= (2/theta_min) q(L) q(R).
```

The second inequality holds because a forced-open run is joined to `T`
whenever one of its endpoints is, so `min(q(L), q(R)) >= theta_min`.

Consequences:

* Every pattern `S` with at most one run on each side of `e_k` has ratio at
  most `2/theta_min`. This includes the full pattern `S = I_k`.
* **One-arm quasi-multiplicativity for every `k`.** The attachment profile
  `g(i,j) = q({e_{i+1},...,e_j})` satisfies
  ```text
  g(0,n) <= g(0,k) + g(k,n) <= (2/theta_min) g(0,k) g(k,n)      for every 0 < k < n.
  ```
  This is the criterion's `g(n) <= C theta^{-1} g(k) g(n-k)`, with `C = 2`,
  for all `k` (not only a positive fraction), on every graph, at every `p'`,
  for the infinite-cluster spine and for every box proxy.

**Corollary 3 (small `r`, uniformly in `n`).** Take an `r`-independent spine
(for example the percolation spine at fixed `p'`). For every `n`,

```text
limsup_{r->0} Br/TJT <= 2/theta_min,       liminf_{r->0} D_n >= (1-2/n) theta_min/2.
```

As `r -> 0` the weights concentrate on the full pattern `S = I_k`, and
Theorem 2 covers that pattern. So in this limit the bridge ratio on paths is
rigorously `O(1/theta)`, which gives `kappa <= 1` in the criterion's
notation.

## What stays open, and what the computation says

For fixed `r > 0`, patterns with several runs on one side of `e_k` carry
weight. There the last-exit argument does not factor, because the runs of
`S^-` may be joined to `T` through the open edges of `S^+`. **Open kernel:**
`K_n(Z) <= C/theta` over multi-run patterns. With Theorem 1 it would give
`Br/TJT <= C/theta` on all path volumes, for all `r`.

**Computation.** `kdecor.c` samples Bernoulli(`p'`) bond percolation in a box
with margin `M` around a straight path of length `n` in `Z^2`, with target
the box boundary. It computes `q(S)`, `q(S^-)`, `q(S^+)` at `k = n/2` for
six patterns: full, alternating, every fourth edge, and three random subsets
of density `1/2`. It then reports `K = q(S)/(q(S^-) q(S^+))` and `K theta`,
where `theta` is the attachment proxy of the middle vertex, with jackknife
errors over 20 batches. The powers of `p'` cancel exactly, so no importance
sampling is needed. Commands:
`gcc -O2 -o kdecor kdecor.c -lm; sh run_all.sh ./kdecor > results.txt`.

**Results** (`results.txt`; `k = n/2`; jackknife errors are in the file.
They are at most `0.015` in `K` for the `M <= 40` rows, and up to `0.2` at
`M = 640`, `n = 64`):

| `n` | `p'`, `M` | `theta` proxy | `K` (full) | max `K` (multi-run) | worst pattern | max `K theta` |
|---|---|---|---|---|---|---|
| 16 | 0.55, 150 | 0.88 | 1.001 | 1.030 | alt | 0.91 |
| 16 | 0.52, 300 | 0.79 | 1.025 | 1.095 | alt | 0.87 |
| 16 | 0.5, 10 | 0.73 | 1.039 | 1.120 | alt | 0.82 |
| 16 | 0.5, 40 | 0.64 | 1.175 | 1.266 | alt | 0.81 |
| 16 | 0.5, 160 | 0.55 | 1.364 | 1.462 | alt | 0.80 |
| 16 | 0.5, 640 | 0.48 | 1.594 | 1.763 | alt | 0.84 |
| 64 | 0.55, 150 | 0.89 | 1.000 | 1.031 | alt | 0.92 |
| 64 | 0.52, 300 | 0.77 | 1.002 | 1.117 | alt | 0.86 |
| 64 | 0.5, 10 | 0.73 | 1.000 | 1.106 | alt | 0.81 |
| 64 | 0.5, 40 | 0.64 | 1.047 | 1.241 | rand2 | 0.79 |
| 64 | 0.5, 160 | 0.55 | 1.195 | 1.400 | rand3 | 0.77 |
| 64 | 0.5, 640 | 0.48 | 1.330 | 1.932 | alt | 0.93 |

What the table shows:

* In this window `K` grows like `1/theta`, not faster. Across a factor of
  about `1.8` in `theta`, `K theta` stays between `0.64` and `0.93` for every
  pattern.
* Every measured ratio is below `1/theta`, a factor of `2` inside the bound
  `2/theta` proved for two runs.
* The worst multi-run pattern exceeds the full pattern by at most about
  `18%` for `M <= 160`. At `M = 640`, `n = 64` the excess is `45%`, with a
  jackknife error of about `15%`. That is the one place where multi-run
  patterns separate from the full pattern, and it is still inside `1/theta`.
* At fixed `theta`, the multi-run maxima at `n = 64` match those at
  `n = 16` within errors, so there is no sign of growth in `n`.

**What this rules out:** in this window no multi-run pattern breaks
`K <= 2/theta`, and the data fit `K ~ c/theta` with `c < 1`. So the open
kernel is not where the Br route fails at bounded density. The scaling in
`theta` is the one that the criterion needs.

**Br route with `C(r) ~ 1/theta(r)`.** Theorem 1 with `K <= C/theta` turns
the criterion's gate into `integral dr / theta(r) < infinity` at the birth
of the spine. That holds for any power-law birth `theta ~ (r - r_c)^beta`
with `beta < 1`, which includes the `Z^2` spine with `beta = 5/36`. It fails
by a logarithm for a linear birth (`beta = 1`), as in mean-field or tree
spines. So the route closes through `K <= C/theta` exactly when the spine is
born sublinearly.
