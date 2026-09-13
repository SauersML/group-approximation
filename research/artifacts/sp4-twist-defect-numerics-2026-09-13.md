---
rg: 2
title: Twist-sector defect numerics for the Sp4(Z) central covers, and the abelian bar as a function of the twist (2026-09-13)
kind: artifact
---

# Status

Numerics only, landed as commentary by lane solve-nh-numerics.
- Every number here is an upper bound on least relator defects, over a finite relator window.
- Nothing here is a lower bound.
- Nothing here is evidence for or against non-hyperlinearity of any group, or for or against any sector floor.
- No node status changes because of this file.

Section 2 (the LP constant) and Section 3 (the larger-dimension descents) are filled in when their jobs finish.

# 0. What main already has, and why this run does not repeat it

`research/artifacts/maslov-mod3-sector-numerics-2026-09-05.md` already ran the direct optimization that the Attempts
of `maslov-mod3-projective-defect-gap` asked for.
- **Presentation.** The eight root generators of `C_2` and every closed loop of length at most `13`: `304,412`
  relators, `17,247` distinct pairs (exponent vector, lift). The lifts `k_r` lie in `{0, 1}`, and exactly `20`
  relators have `k_r = 1`, all of length `12` in the two long-root copies of `SL_2(Z)`.
- **Exact seeds.** The metaplectic class `(-1)^(k_r)` is realized exactly in dimensions `4` and `10`
  (`sp4-second-order-thetas-realize-metaplectic-class-in-dim-four`,
  `sp4-even-theta-constants-realize-the-metaplectic-class`), hence in every dimension `4a + 10b`.
- **Result at theta = 1/3.**
  - Random-start local search is blind: it doesn't even find exact metaplectic models.
  - The best coboundary rescaling of the metaplectic seed has maximal defect `0.3090` on all relators.
  - Smoothed-maximum descents at `d = 4, 8, 10, 12` return to that coboundary point.
- **Structural blindness.** `maslov-bounded-block-sector-gap` proves a floor on every fixed block-size stratum. So any
  falsifying sequence must carry asymptotically all dimension in irreducible blocks of unbounded size. That is
  exactly the regime local search in small dimension cannot reach.

So rerunning random-start descents at theta = 1/3 in `d = 8..256` would repeat a recorded dead instrument. This file
adds three things instead:
1. the abelian (coboundary) bar as a function of the twist `theta`, including irrational `theta`;
2. its exact constant, from a linear program over all relator rows;
3. seeded descents at `d = 20, 30, 40`.

# 1. The abelian bar as a function of theta (job 705107)

**Setup.**
- Let `rho` be an exact projective model with scalar relator values `s_r I`: `s_r = (-1)^(k_r)` for the metaplectic
  seeds, `s_r = 1` for the trivial representation.
- Rescale the generators by phases `e^(i phi_s)`. In the theta-sector the target is `exp(2 pi i theta k_r) I`, so the
  normalized-HS defect of relator `r` is `|exp(i <e_r, phi>) s_r - exp(2 pi i theta k_r)|`. That quantity doesn't
  depend on the dimension of the seed.
- Tensoring with `1_m` preserves it. So the minimax over `phi` is an explicit upper bound on the least maximal relator
  defect over this window, in every dimension `4a + 10b` (metaplectic seed) or every `d` (trivial seed).
- `theta_bar_profile.py` minimizes the smoothed maximum from `24` starts, then evaluates the exact maximum over all
  `17,247` distinct rows at the returned `phi`. So each number below is a valid upper bound, not merely an
  optimizer value.

**Data** (`theta_bar_profile.tsv`). `delta = dist(theta, (1/2)Z)`, bar = best of the two seeds, implied
`kappa = arcsin(bar/2) / (pi delta)`:

```text
theta              delta      metaplectic   trivial    bar        implied kappa
0.5                0          0             (1.945*)   0          -
0.49               0.01       0.048763      0.875277   0.048763   (0.776, smoothing artifact)
0.45               0.05       0.094217      0.808254   0.094217   0.300
0.414214 (sqrt2-1) 0.085786   0.160336      0.747358   0.160336   0.298
0.4                0.1        0.186300      0.722944   0.186300   0.2969
0.618034 (golden)  0.118034   0.219202      0.691789   0.219202   0.2962
1/3                1/6        0.307861      0.606854   0.307861   0.2952
0.3                0.2        0.368400      0.547933   0.368400   0.2949
0.25               0.25       0.458626      0.458626   0.458626   0.2946
0.2                0.2        0.547933      0.368400   0.368400   0.2949
1/6                1/6        0.606854      0.307861   0.307861   0.2952
0.1                0.1        0.722944      0.186300   0.186300   0.2969
0.05               0.05       0.808254      0.094217   0.094217   0.300
0.0                0          (1.902*)      0          0          -
```

Reading the two seed columns against `delta` measured from each seed's own parameter (`1/2` for metaplectic, `0` for
trivial):

```text
delta from the seed's parameter   0.1      1/6      0.2      0.25     0.3      1/3      0.4      0.45     0.49
bar                               0.1863   0.3079   0.3684   0.4586   0.5479   0.6069   0.7229   0.8083   0.8753
implied kappa                     0.2969   0.2952   0.2949   0.2946   0.2945   0.2944   0.2943   0.2943   0.2943
```

`(*)`: at `delta = 1/2` the random-start optimizer stalls at the symmetric saddle `phi = 0`. The linear bound below
gives about `0.89` there, so those two values are optimizer failures, not bars.

**Observations.**
- **Only the distance matters.** The bar depends only on `delta` measured from the seed's parameter. That is forced by
  construction, since `(-1)^k = exp(2 pi i k/2)`, and the table reproduces it to six digits.
- **Linear form.** Writing `phi = 2 pi delta psi`, the defect is `2|sin(pi delta (<e_r, psi> - k_r))|`. So
  `bar <= 2 sin(pi delta kappa*)` with `kappa* = min_psi max_r |<e_r, psi> - k_r|`, whenever `delta kappa* <= 1/2`.
  The implied `kappa` settles at about `0.2943` from above as `delta` grows. At small `delta` the log-sum-exp
  smoothing term (`log(1/17247)/800`, about `-0.012` in squared units) is comparable to the defects, so the optimizer
  is inaccurate there and the implied values are too large. Section 2 computes `kappa*` exactly.
- **Only long roots move.** At every `theta` the optimal phases move only the four long-root generators, positive roots
  by `-s` and negative roots by `+s`: the coordinates of the twenty lifted relators.

# 2. The exact constant kappa* = 5/17 (job 708823)

`lp_kappa.py`, log `lpkappa.708823.log`.

**LP.** A cutting-plane LP over all `17,247` distinct rows converges in two iterations, with interior point on at most
`523` active rows. Float optimum: `0.294117647264`.

**Exact upper bound.** Rational arithmetic over every row: `psi_q = (1/17, 1/17, 0, 0, -1/17, -1/17, 0, 0)` gives
`max_r |<e_r, psi_q> - k_r| = 5/17` exactly. So `kappa* <= 5/17`.

**Lower bound, exact** (job 709305: `lp_dual_exact.py`, log `lpdual.709305.log`).
- At `psi_q`, `27` rows are active. A simplex vertex of `{w >= 0, sum w s_r e_r = 0, sum w = 1}` on those rows has
  support `8`. Solving over `Q` on the support gives an exact certificate:

```text
sign  exponent vector (letters 0..7)   lift   weight
 +1   [0, 2, 0, 0, -3, 0, 0, -1]        0      12/187
 +1   [0, 2, 0, 0, -3, 0, 0,  1]        0      12/187
 -1   [0, 9, 0, 0, 0, -3, 0, 0]         1      31/187
 +1   [2, 0, 0, -1, 0, -3, 0, 0]        0      31/374
 +1   [2, 0, 0,  1, 0, -3, 0, 0]        0      31/374
 +1   [2, 3, -1, 0, 0, 0, 0, 0]         0      7/34
 +1   [2, 3,  1, 0, 0, 0, 0, 0]         0      7/34
 -1   [9, 0, 0, 0, -3, 0, 0, 0]         1      24/187
```

- The weights balance the exponent vectors exactly. So for every `psi`,
  `max_r |<e_r, psi> - k_r| >= sum w s_r (<e_r, psi> - k_r) = -sum w s_r k_r = 5/17`.
- With the upper bound, **`kappa* = 5/17` exactly**, over the distinct rows of this window. The two rows with lift
  `1` are exponent vectors of long-root words: `9` letters of one long positive root against `3` of the other sign.

**Consequence, exact over this window.**
- Take the exact seed rescaled by `phi = 2 pi delta' psi_q`, with signed `delta' = theta - 1/2` for the metaplectic seed
  or `delta' = theta` for the trivial one. Relator `r` then has defect `2|sin(pi delta' (<e_r, psi_q> - k_r))|`.
- Its maximum over all `304,412` relators is exactly `2 sin(5 pi |delta'| / 17)`, for every `|delta'| <= 1/2`.
- So, in every dimension `4a + 10b` (from the metaplectic seed) and in every `d` (from the trivial seed):

```text
bar(theta)  <=  2 sin( 5 pi dist(theta, (1/2)Z) / 17 ).
```

```text
delta    1/10       1/6        1/4        1/3        1/2
bound    0.184537   0.306783   0.457901   0.606305   0.891477
```

**Observations.**
- **Theta = 1/3.** The bound is `2 sin(5 pi/102) = 0.306783`. That is slightly below both the recorded bar `0.3090`
  (2026-09-05 artifact, which a nonabelian search had to beat) and this run's optimizer value `0.307861`. So the
  corrected bar over this window is `0.306783`.
- **Other branches.** `kappa*` is the optimum only among phases of the linear form `2 pi delta' psi`. Other branches
  (integer shifts of `<e_r, phi>`) aren't excluded exactly, but the 24-start global search at `delta >= 0.05` never
  found one that does better.
- **Scope.** All of this concerns abelian relaxations of exact seeds over a finite window. None of it is a sector lower
  bound.

# 3. Seeded descents at d = 20, 30, 40 (job pending)

[pending]

# 4. What this suggests for the two live routes

**One non-embeddable twist (lane solve-nh-twist).**
- **The bar.** It is a continuous, dimension-free upper-bound curve over this window. It vanishes linearly at `theta in
  (1/2)Z` and is at most `2 sin(pi delta kappa*)` everywhere, irrational `theta` included.
- **What it can't show.** Coboundary relaxations never improve with dimension, and small-dimension nonabelian descents
  don't beat the bar (Section 0; Section 3 when filled). By `maslov-bounded-block-sector-gap` both instruments are
  blind to the only possible countermodels. So these numbers give neither kill evidence against the twist route nor
  support for it.
- **What survives.** The route is untouched: an embeddable twist would need models with unbounded irreducible blocks,
  and nothing here builds those.

**Regular-character rounding (lane solve-nh-rcr).** No numerics were run.
- **Why the easy side is uninformative.** Genuine representations with limit trace `delta_e` exist trivially, e.g. the
  permutation representations of `Sp4(Z)` on `F_p^4 \ {0}` as `p -> infinity`.
- **What the kill test needs.** An asymptotic representation with trace tending to `delta_e` that stays far from every
  genuine representation.
- **Why no instrument here helps.** Distance to the set of genuine representations isn't computable by local search.
  Any numerical near-representation found in small dimension is automatically close to something in that dimension,
  by compactness.

# 5. Files

`research/artifacts/sp4-twist-defect-numerics-2026-09-13/`:
- `theta_bar_profile.py`, `thetabar.sbatch`, `theta_bar_profile.tsv`, `thetabar.705107.log` (Section 1);
- `lp_kappa.py`, `lp.sbatch` (Section 2);
- `make_seeds_nh.py`, `descent.sbatch` (Section 3).

The relator file `pres6.json` (`13.5 MB`, md5 `3b6b79835437ee157005e7fa65cd3671`) is regenerated by
`experiments/maslov_sector/presentation.py 6 13 pres6.json` in about six minutes. The descent script is
`experiments/maslov_sector/optimize7.py` on main, unchanged.
