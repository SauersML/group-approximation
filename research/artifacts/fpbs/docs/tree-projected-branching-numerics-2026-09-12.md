# Tree-projected percolation: fibre profiles, half-graph factors and sphere bubbles near p_c

Lane `bs-pc-pu-2`, 2026-09-12.

**Evidence, not proof.** All numbers below come from a Monte Carlo explorer,
`experiments/fpbs-tree-projected-mc/tpmc.c` (commit 483af644a). It explores the
cluster of the identity lazily on the infinite graph, stopping at a size cap.
Error bars are ±1 standard error from 20 batch means.

Every quantity here is nondecreasing in `p`. So a value measured at a
parameter that is truly subcritical is a lower bound for its critical left
limit. A run is called *capped-free* when none of its explorations reached the
cap.

## 1. Graphs and quantities

The group is `F_2 x Z`. The generating sets project into `{1, a^±1, b^±1}`:

| label | generators (with inverses) | degree |
|---|---|---|
| G1 | `(a,0),(a,1),(b,0),(1,1)` (the asymmetric example of artifact Section 4.3) | 8 |
| G2 | `(a,0),(b,0),(1,1)`: the product `T_4 □ Z` (symmetric control) | 6 |
| G3 | `(a,0),(b,0),(1,z)` for `z = 1..5` | 14 |
| G4 | `(a,t)` for `t = 0..3`, `(b,0),(1,1)` | 12 |

Measured quantities:
* `chi = E|K_o|`;
* `chi^H = sigma(1)`;
* `sigma(s) = E|K_o ∩ Gamma_s|`;
* `B = sum_q sigma(q)^2`;
* `lambda(s) = p m_s chi^(s)`, where `chi^(s)` is the relative susceptibility
  of the half graph missing branch `s^(-1)`;
* `b_R = sum_(|q|=R) sigma(q)^2`, estimated as `E sum m_1(q) m_2(q)` over two
  independent clusters;
* `rho(N)`, the spectral radius of `N(s,t) = lambda(t)^2 1{t != s^(-1)}`.

By the symmetries `a <-> A` and `b <-> B`, `rho(N)` is the Perron root of
`[[lambda_a^2, 2 lambda_b^2], [2 lambda_a^2, lambda_b^2]]`.

**Cross-check.** At `p = 0.05` on G1 this code agrees within about 2 SE with
an independent Python explorer (`experiments/bs-pc-pu/fibre_profile_mc.py`):
* `chi` is 1.610 ± 0.008 here against 1.628 there;
* `chi^H` is 1.118 ± 0.002 against 1.121;
* `B` is 1.292 ± 0.005 against 1.296.

Two identities also hold numerically:
* `sigma(a) = sigma(A)` within error, as required by `sigma(q^(-1)) = sigma(q)`;
* the inequalities of `fpbs-tree-projected-branch-share-last-crossing-bound`.

## 2. p_c brackets

**Scan design.**
* *Coarse scan:* `N = 2000`, cap `2·10^5`.
* *Refined scan:* `N = 4000`, cap `2·10^6`, a 240 s limit per run, 4 cores on
  MSI.
* A run with truncated clusters is treated as at or above `p_c`.
* *Linear extrapolation* of `1/chi` from capped-free runs gives the point
  estimates. This assumes mean-field `chi ≍ (p_c - p)^(-1)`.

| graph | capped-free p (chi) | first capped p (fraction of explorations capped) | p_c estimate |
|---|---|---|---|
| G1 | 0.150 (28.3 ± 1.5), 0.153 (45.6 ± 3.3), 0.156 (90 ± 9) | 0.160 (2.6%) | about 0.158–0.159 |
| G2 | 0.205 (40.8 ± 2.5), 0.210 (148 ± 15) | 0.213 (2.4%) | about 0.212 |
| G3 | 0.085 (33.0 ± 1.5), 0.089 (121 ± 9) | 0.092 and 0.095 timed out | about 0.090–0.091 |
| G4 | 0.100 (53 ± 5; coarse scan) | 0.103 (0.6%) | in (0.100, 0.103) |

## 3. Values at the largest capped-free parameter

| graph, p | chi^H | sigma(a) | sigma(b) | lambda(a) | lambda(b) | rho(N) | B |
|---|---|---|---|---|---|---|---|
| G1, 0.156 | 1.645 ± 0.016 | 0.720 ± 0.020 | 0.398 ± 0.012 | 0.471 ± 0.005 | 0.255 ± 0.003 | 0.40 ± 0.01 | 4.72 ± 0.13 |
| G2, 0.210 | 1.697 ± 0.016 | 0.544 ± 0.014 | 0.547 ± 0.014 | 0.351 ± 0.003 | 0.347 ± 0.003 | 0.37 ± 0.01 | 4.61 ± 0.09 |
| G3, 0.089 | 4.22 ± 0.06 | 1.32 ± 0.06 | 1.38 ± 0.05 | 0.353 ± 0.005 | 0.360 ± 0.005 | 0.38 ± 0.01 | 26.5 ± 1.1 |
| G4, 0.100 (coarse) | 1.77 ± 0.03 | 0.92 ± 0.03 | 0.288 ± 0.017 | 0.603 ± 0.009 | 0.178 ± 0.003 | 0.47 ± 0.01 | 6.2 ± 0.4 |

**Trend on G1.** Over `p = 0.145, 0.150, 0.153, 0.156`:
* `chi` grows from 18 to 90;
* `lambda(a)` is 0.418, 0.446, 0.465, 0.471;
* `rho(N)` is 0.31, 0.35, 0.38, 0.40.

It rises slowly, with no sign of approaching 1. The mean-field prediction at
`p_c` is `1/(2n-1) = 1/3`.

## 4. Fibre-sphere bubbles

| graph, p | b_0 | b_1 | b_2 | b_3 | b_4 |
|---|---|---|---|---|---|
| G1, 0.156 | 2.73 ± 0.04 | 1.32 ± 0.05 | 0.44 ± 0.03 | 0.152 ± 0.016 | 0.060 ± 0.015 |
| G2, 0.210 | 2.91 ± 0.03 | 1.19 ± 0.05 | 0.36 ± 0.03 | 0.114 ± 0.018 | 0.027 ± 0.005 |
| G3, 0.089 | 17.2 ± 0.6 | 6.68 ± 0.34 | 1.89 ± 0.23 | 0.43 ± 0.09 | 0.12 ± 0.04 |
| G4, 0.103 (0.6% capped) | 3.54 ± 0.07 | 2.30 ± 0.09 | 0.97 ± 0.07 | 0.37 ± 0.04 | 0.15 ± 0.02 |

**Decay rates.** The successive ratios `b_(R+1)/b_R` for `R >= 1` lie between
0.22 and 0.48. On G1 they are 0.33, 0.35 and 0.39. That is the order of the
mean-field rate `beta = 1/(2n-1)`.

## 5. What the numbers bear on

1. **Radius one is dead as a target.** `b_1 > 1` already holds below `p_c` on
   all four graphs, and markedly so on G3 and G4. So the finite radius in
   `fpbs-tree-projected-critical-sphere-bubble-below-one` must be `R >= 2`, and
   `R >= 3` for G3. Since `b_R` increases with `p`, these are genuine failures
   of `b_1(p_c) < 1` whenever the runs are subcritical.
2. **The first-hit nearest-fibre bound fails on G3.** Artifact Section 4.3 asks
   for `sup_(p<p_c) max_s sigma_p(s) < 1`. On G3 at the capped-free parameter
   `p = 0.089`, `sigma(b) = 1.38 ± 0.05` and `sigma(a) = 1.32 ± 0.06`.
3. **The half-graph transfer condition has room.** `rho(N)` lies between 0.37
   and 0.47 at the largest capped-free parameters. That is the condition of
   `fpbs-tree-projected-critical-half-graph-transfer-below-one`, together with
   `chi^H` between 1.6 and 4.2.
4. **The last-crossing bound holds with moderate slack.** On G1 at `p = 0.156`
   it gives `b_1 <= (chi^H)^2 sum_s lambda(s)^2 = 1.55` (measured 1.32) and
   `b_2 <= 0.60` (measured 0.44). On G3 at `p = 0.089` it gives `b_1 <= 9.1`
   (measured 6.7).

## 6. Limits

* **Truncation.** Near `p_c` heavy tails make `chi` noisy, and the largest runs
  on G3 and G4 timed out. Critical values are left limits and exceed every
  number here.
* **Cutoff.** Caps of `2·10^6` sit well above `chi^2` at the capped-free
  parameters, so truncation bias there should be small. It is not zero.
* **G4 at 0.103** had 0.6% of explorations truncated and is at or just above
  `p_c`. Its bubble values are biased low by truncation.
* **Scope.** No claim here depends on these numbers.

MSI outputs: `/scratch.global/sauer354/bs-pc-pu-2/scan1/` and `scan2/`.
