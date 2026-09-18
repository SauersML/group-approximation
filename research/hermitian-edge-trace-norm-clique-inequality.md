---
rg: 2
id: hermitian-edge-trace-norm-clique-inequality
kind: claim
title: Uniform clique inequality - a Hermitian matrix with zero diagonal and all off-diagonal moduli at least 1 has trace norm at least sqrt3 (m-1)
artifacts:
  - experiments/hermitian-edge-trace-norm-2026-09-18/README.md
  - experiments/hermitian-edge-trace-norm-clique-energy-2026-09-18/README.md
  - experiments/hermitian-edge-trace-norm-clique-small-m-2026-09-18/README.md
distinct_from:
  hermitian-edge-trace-norm-vs-independence: that is (**) for every graph and weight; this is the single case G = K_m, w = 1, which by the facet reduction is equivalent to (**) for all h-perfect graphs (all perfect graphs) and is the only open case there.
---

**OPEN only for m = 5.** It is proved for `m <= 3`, for `m = 4` by `hermitian-edge-trace-norm-clique-inequality-k4` (computer-assisted flux-torus branch-and-bound), and for every `m >= 6` by `hermitian-edge-trace-norm-clique-inequality-large-m`. Numerics cover `m <= 10`. For every `m >= 2` and every Hermitian
`m x m` matrix `C` with `C_ii = 0` and `|C_ij| >= 1` for all `i != j`,

```text
(UCI)     || C ||_1  >=  sqrt3 (m - 1) .
```

**Why it matters.** By `hermitian-edge-trace-norm-k4-free-h-perfect` (Theorem C), (UCI) for all `m`
is equivalent to (**) for all perfect graphs and all h-perfect graphs, and it is one of the two
holes of `hermitian-edge-trace-norm-via-stab-facets`. (UCI) with `m <= 3` is what gives the proved
class (K4-free h-perfect graphs). `K_5` is now the only open instance (`K_4` is done).

**Equivalent forms.**
- *Dual.* (UCI) iff `sum_i Q_ii >= sqrt3 (m-1)` whenever `Q +- C >= 0`. With `A = (Q+C)/2`,
  `B = (Q-C)/2`: two PSD matrices with equal diagonals `d_i` and `|A_ij - B_ij| >= 1` for `i != j`
  must have `sum d_i >= (sqrt3/2)(m-1)`. In Gram form: vectors `a_i, b_i` with `|a_i| = |b_i|` and
  `|<a_i,a_j> - <b_i,b_j>| >= 1` for all `i != j`.
- *Weighted.* By the facet reduction, (UCI) for all `s <= m` is equivalent to (**) for `K_m` with
  every weight `w`.

**Status after w6-078 (2026-09-18).** `hermitian-edge-trace-norm-clique-inequality-large-m` proves (UCI)
for all `m >= 6`. The proof is a rank-one reduction, averaging, and a computer-verified Yudin-type LP
certificate on the complex sphere. What is left:

- *Rank-one reduction (proved there, Step 1).* Put `A = C_+`, `B = C_-` with common diagonal `d`.
  Einollahzadeh's lemma and the Schur product `conj(A) o B` give unit vectors with Gram matrix `G` such
  that `d_i d_j |1 - G_ij|^2 >= 1` for `i != j`. Also, `K = sqrt d sqrt d^T - X(conj(A) o B)X` is
  admissible, has one positive eigenvalue, and `||K||_1 <= ||C||_1`. So it suffices to treat matrices
  with exactly one positive eigenvalue, which explains the numerics below.
- *The open core, `(M_m)` for `m = 4, 5`.* (UCI) for size `m` follows from
  `2 nu_f(r) >= (sqrt3/2)(m-1)`, where `r_ij = 1/|1 - G_ij|` for unit vectors with Gram matrix `G`, and
  `nu_f` is the maximum `r`-weight of a fractional perfect matching of `K_m`.
  - For `m = 4` this reads: *among the three perfect matchings of 4 unit vectors, one has
    `r_ij + r_kl >= 3 sqrt3/4`.*
  - The numerical minima of `2 nu_f` are `1 + sqrt3` (`m = 4`) and `(5 + sqrt5)/2` (`m = 5`), exactly
    half the minima of `||C||_1`. So nothing is lost.
- *Obstruction.* Any bound through `sum d >= E(G)/(m-1)`, with `E = sum_{i != j} r_ij`, fails at
  `m = 4, 5`. The 4th and 5th roots of unity give `E = 2 + 4 sqrt2 = 7.657` and `E = 13.764`,
  below the needed `(sqrt3/2)(m-1)^2 = 7.794` and `13.856`. So `m = 4, 5` need the matching (non-averaged) structure.

- *`m = 4` and the route for `m = 5`.* `hermitian-edge-trace-norm-clique-inequality-k4` proves `m = 4`
  directly. After gauging, only the flux torus `T^3` is free. For fixed phases the problem is an SDP,
  whose dual `Z` gives the separable lower bound `sum t_ij 2Re(Z_ji e^{i theta_ij})`. This covers `T^3`
  with 584 boxes carrying exactly checked rational certificates. The same script runs `m = 5` on `T^6`
  (with a 4-fold symmetry reduction). About 41,000 SDP solves cover one sixteenth of the reduced
  domain, and the run is in progress.

**Known.** `m = 2`: `||C||_1 = 2|C_12|`. `m = 3`: `tr C = 0` gives `||C||_1 >= sqrt2 ||C||_F >= 2 sqrt3`,
tight at flux `pi/2`. Frobenius alone gives `sqrt(2m(m-1))`, which is below `sqrt3 (m-1)` for `m >= 4`.
Since `tr C = 0`, `||C||_1 >= 2 ||C||_op`, but `||C||_op` can be as small as about `sqrt(m-1)` for
random-like phases, so this is useful only together with a bound that is strong when `||C||_op` is small.

**Numerics** (`experiments/hermitian-edge-trace-norm-2026-09-18/clique_min.py`, L-BFGS-B over moduli
and phases with many restarts). The minimum of `||C||_1 / (sqrt3 (m-1))`:

| m | min `||C||_1` | ratio | spectrum at the optimum |
|---|---|---|---|
| 3 | 3.4641 = 2 sqrt3 | 1.000 | `-sqrt3, 0, sqrt3` |
| 4 | 5.4641 = 2 + 2 sqrt3 | 1.052 | `-2, -0.732, 0, 2.732` |
| 5 | 7.2362 = 5 + sqrt5 | 1.044 | `-3.618, 0, 0, 1.382, 2.236` |
| 6 | 9.2542 | 1.069 | one negative eigenvalue `-4.627` |
| 7 | 11.1294 | 1.071 | one negative eigenvalue `-5.565` |
| 8 | 13.2080 | 1.089 | one negative eigenvalue `-6.604` |
| 10 | 17.1083 | 1.098 | one negative eigenvalue `-8.554` |

All optima have unit moduli, and (up to sign, `C -> -C`) one eigenvalue of one sign, so
`||C||_1 = 2 ||C||_op`. In the dual picture one of `A, B` has rank 1. Then, in the gauge `b_i = sqrt(d_i)`,
`C_ij = sqrt(d_i d_j) (<u_i,u_j> - 1)` with unit vectors `u_i`, and (UCI) in this regime reads
`d_i d_j |1 - <u_i,u_j>|^2 >= 1 => sum d_i >= (sqrt3/2)(m-1)`. The ratio seems to increase slowly
with `m`; a weak-limit heuristic suggests `min ||C||_1 ~ 2m`.
