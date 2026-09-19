---
rg: 2
id: dkkms-seed-law-is-uniform-in-regime-and-far-in-window
kind: claim
title: At the DKKMS smoothing rate beta = log log k / k the seed law of the 2-to-1 edge process is conditionally uniform at almost every A-vertex throughout the rigidity regime, so the seed-concentration hypothesis of the smoothing obstruction fails at every certified point, while on the admissible q = 1 window below 4^(l-1)/12 the seed law is at total variation at least 3/4 - 1/ln k from every transitive law, so no covering or coupling transfer reaches that window and the local rigidity target splits into a proved certified half and a window half that nothing uses
distinct_from:
  dkkms-grassmann-2to1-test-is-locally-99-percent-rigid: that is the OPEN rigidity statement quantified over every k admissible for Corollary A; this splits it into T1 (certified points, proved here by composition) and T2 (the uncertified q = 1 window), and proves that the one known proof technique cannot reach T2.
  dkkms-near-perfect-labellings-are-outer-honest: that proves rigidity when SD* <= 10^(-5) from an upper bound on the covering distance and leaves k < k_0(l) as not covered; this gives the matching lower bound, showing that on [k_A(l), 4^(l-1)/12] the distance itself is >= 3/4 - 1/ln k, not merely its bound, and it adds the conditional (per A-vertex) form of the upper bound.
  dkkms-smoothing-leaves-the-branch-coordinate-untested: that measures seed concentration at the fixed rate beta = 0.3 or 0.5, reads it as the direction the DKKMS parameters go, and states Proposition 4 conditional on it; this proves that at the paper's rate the conditional seed law is within 5*10^(-5) of uniform on average in the whole regime (R), so the Proposition 4 labelling has value below 1/7 there, and measures the same reversal at every tested small (l, k).
  dkkms-certified-parameters-lie-in-the-selector-kill-regime: that places every certified point in the regime (R)+(A) and closes the selector hole; this uses that placement to discharge the rigidity target at those points and identifies what is left of the target as a statement about uncertified parameters only.
  grassmann-restriction-test-is-99-percent-rigid: that is rigidity for the plain Grassmann restriction test on one ambient space; this is about how far the DKKMS seed law is from that test's law, in both directions.
artifacts:
  - experiments/dkkms-covering-window-2026-09-17/seed_law_at_dkkms_beta.py
---

**ESTABLISHED.** Route: `dkkms-seed-law-is-uniform-in-regime-and-far-in-window-proof`.

## Setting

The notation is that of `dkkms-near-perfect-labellings-are-outer-honest` and
its route.

- `U` is a k-tuple of variable-disjoint weight-3 equations, with
  `X_U = F_2^(3k)` split into `k` blocks of 3 coordinates. `H_U` is spanned by
  the `k` block all-ones vectors.
- `V` keeps each equation with probability `1 - beta`. Otherwise it keeps one
  uniform variable of that block. `X_V` is the span of the kept coordinates,
  and `beta = log log k / k`, in either the natural or the base-2 reading.
- The per-tuple edge law `P` given `U` draws
  - `V`;
  - a seed `R` uniform in `Gr(X_V, l-1)`;
  - an A-space `L > R` uniform in `Gr(X_U, l)`.

  It then restricts to `L meet H_U = 0` and renormalises.

The seed laws:

- `P0` is the law of `R` before the restriction, that is, the law `L'` of
  DKKMS Definition 4.8 at dimension `l - 1`.
- `Q` is the uniform law on `Gr(X_U, l-1)`.
- `nu0` is the ideal edge law: `R` uniform among `(l-1)`-spaces with
  `R meet H_U = 0`, then `L` a uniform valid extension.

For a valid `L`, `w(. | L) := P(R = . | L)` is the conditional seed law. It
lives on the `2^l - 1` hyperplanes of `L`, and `u_L` is the uniform law on
them.

The quantities:

- `d(l,k) := beta sqrt(k) 2^(l+3)` is the covering bound, and `SD*` is as in
  the outer-honest node.
- `k_A(l) := e^l (2 l ln 2 + ln(4 * 192^2))` is the least `k` admissible for
  Corollary A at advice dimension `q = 1`, that is, the least `k` with
  `eps_k = exp(-k/e^l) <= p0^2/4` and `p0 = 2^(-l)/192`.
- `k_T(l) := 4^(l-1)/12`.

## Statements

**Theorem U (conditional uniformity in the regime).** Let `l >= 3`,
`2^(l-1) beta <= 1/8` and `2^(l-1-k) <= 1/3`. Then

```text
E_(L ~ P) TV( w(.|L), u_L )  <=  6 d(l,k),       so
E_(L ~ P) max_R w(R|L)       <=  1/(2^l - 1) + 6 d(l,k).
```

Under (R) (`SD* <= 10^(-5)`) the right-hand sides are `<= 6 * 10^(-5)` and
`<= 1/7 + 6 * 10^(-5)`.

**Theorem W (distance in the window).** For every `beta` in `[0, 1]`, every
`l >= 2` and every `k >= l - 1` (so that `P0` is defined),

```text
TV(P0, Q)                 >=  1 - (1 - beta)^k - 3 k 4^(1-l),
TV(P_seed, nu0_seed)      >=  1 - (1 - beta)^k - 3 k 4^(1-l) - 2^(l-1-k) - 2^(l-2k),
```

where `P_seed` and `nu0_seed` are the seed marginals of `P` and `nu0`. The
same lower bound holds against every law of `(l-1)`-spaces that is invariant
under a group acting transitively on `Gr(X_U, l-1)`, because such a law is
`Q`. At `beta = log log k / k`, `(1 - beta)^k <= 1/ln k` in both readings. So
for `k_A(l) <= k <= k_T(l)`,

```text
TV(P0, Q)  >=  3/4 - 1/ln k        and        TV(P_seed, nu0_seed)  >=  3/4 - 1/ln k - 2^(1+l-k).
```

The interval `[k_A(l), k_T(l)]` is non-empty for every `l >= 20`, and its
length ratio `k_T/k_A` grows like `(4/e)^l / l`.

**Corollary T (the target splits).** Write `T` for
`dkkms-grassmann-2to1-test-is-locally-99-percent-rigid`.

- `T1` is `T` restricted to admissible points in (R), that is, with
  `SD* <= 10^(-5)`.
- `T2` is `T` restricted to admissible points outside (R).

Then:

1. `T1` holds, with `eta_1 = 10^(-5)`, `zeta_1 = 1/128`, outer value
   `>= 15/16` and dirt `<= 1/64`. In particular `T` holds at every
   DKKMS-certified point with `l >= 5`.
2. `T` holds if and only if `T2` holds. The constants combine as the minimum of
   the two `eta_1` values, the maximum of the two `zeta_1` values and the
   maximum of the two `l_0` values. `T2` contains no certified point with
   `l >= 5`.
3. At `q = 1`, every `k` in `[k_A(l), k_T(l)]` is a point of `T2`. At such a
   point the per-tuple transfer step of the only recorded proof of `T` loses
   total variation `>= 3/4 - 1/ln k - 3 * 2^(l-k)`. That step is inequality
   (2) of the outer-honest route, and the loss is `>= 1/2` for every
   `l >= 20`.

**Corollary P4 (the smoothing obstruction is vacuous where it matters).**
Proposition 4 of `dkkms-smoothing-leaves-the-branch-coordinate-untested`
assumes weight `>= 1 - xi` on the generating seed for a `1 - delta` fraction of
the A-mass. At every point satisfying the hypotheses of Theorem U with
`6 d <= 10^(-4)`, and in particular at every point of (R) and every certified
point with `l >= 5`, that assumption forces
`(1 - delta)(1 - xi) <= 1/7 + 10^(-4)`. So the value that Proposition 4
guarantees, `1 - delta - delta' - xi`, is below `0.1431`, whatever the folding
hypothesis gives. The dominant-hyperplane labelling itself has value
`E max_R w(R|L) <= 1/7 + 10^(-4)`. Neither comes near the `1 - eta_1` needed to
refute `T`.

## What it does (impact types 2, 3 and 4)

* **Decomposition (type 2).** The last open prerequisite on the DKKMS route to
  the 2-to-2 statement, the rigidity target `T`, is quantified over every `k`
  admissible for Corollary A. It now splits into two pieces that fail
  separately. `T1` is the (R) part and follows from Corollary N of
  `dkkms-near-perfect-labellings-are-outer-honest`. By Theorem C of
  `dkkms-certified-parameters-lie-in-the-selector-kill-regime`, `T1` contains
  every certified point with `l >= 5`. `T2` is the rest, and it contains no
  certified point. The DKKMS soundness chain instantiates only certified
  points, and so does the selector kill of the certified-parameters node. So on
  that route `T` is discharged, and what remains open, `T2`, is a stronger
  statement than the route needs. This node does not check whether some other
  recorded consumer of `T` needs uncertified points. The target's quantifier should be narrowed
  to certified points, or `T2` should be split off as a separate claim.
* **Class killed (type 3).** The class is every proof of `T2` that transfers
  rigidity per tuple from a transitive (uniform) Grassmann test to the DKKMS
  seed law. That includes a coupling, a covering-lemma bound, a
  statistical-distance transfer of rejection probabilities, or a mixture with
  a `GL`-invariant test.
  - **Invariant:** `TV(P_seed, nu0_seed)`, the distance between the seed
    marginal of the edge law and the uniform seed law.
  - **Where every member dies:** step (2) of the outer-honest route,
    `rej_Q <= 2 eta_U + SD(P, Q)`. On the window `[k_A(l), k_T(l)]` the
    distance `SD(P, Q)` is at least `3/4 - 1/ln k - 3 * 2^(l-k) >= 1/2`
    (Theorem W), so the inequality cannot give `rej_Q < 1/2`.
  - **Why no member escapes:** the obstruction is the law itself, not a lossy
    bound. With probability `>= 1 - 1/ln k` the smoothed blocks force a block
    projection of the seed into a coordinate axis. A uniform `(l-1)`-space does
    that with probability `<= 3k 4^(1-l) <= 1/4`.
* **Reversal (type 4).** `dkkms-smoothing-leaves-the-branch-coordinate-untested`
  measured seed concentration at the fixed rate `beta = 0.3, 0.5` and read it
  as "the direction the DKKMS parameters go". At the paper's rate
  `beta = log log k / k` the direction is the opposite. The conditional seed law
  at a typical A-vertex converges to uniform on the `2^l - 1` hyperplanes, with
  average distance `<= 6 d(l,k)` (Theorem U). So Proposition 4 there has a
  hypothesis that fails at every certified point (Corollary P4).
  - The smoothing does not leave the branch coordinate untested in the regime.
    Every A-vertex is tested through essentially all its hyperplanes, as the
    six-flag gadget of Theorem R needs.
  - The artifact measures this at small `(l, k)`. At `l = 3`, `E max w` is
    `0.2369, 0.1451, 0.1429` at `k = 2^6, 2^18, 2^30`, against the uniform
    value `1/7 = 0.1429`.

This neither proves nor refutes UGC.

## Numerical evidence

The artifact `experiments/dkkms-covering-window-2026-09-17/seed_law_at_dkkms_beta.py`
(seed `20260917`, exit 0) checks the following.

1. **Closed form of `P0/Q`.** Put `a = 4^(l-1)`. Then
   `P0(R)/Q(R) = (1-beta)^k (1 + beta a/(1-beta))^(n0) (1 + beta a/(3(1-beta)))^(n1)`
   up to relative error `4 l 2^(l-k)`. Here `n0` is the number of blocks where
   `proj(R) = 0`, and `n1` the number where `proj(R)` is a coordinate axis. The
   measured error against the exact dynamic program of
   `seed_spread_dkkms.py` is `<= 1.3 * 10^(-4)`.
2. **Block sampler.** The fast sampler reproduces the explicit sampler within
   Monte Carlo error. At `l = 3` the mean top share is `0.2800` against
   `0.2856` at `k = 10`, and `0.2805` against `0.2840` at `k = 12`.
3. **Covering tightness.** `TV(P0, Q)` estimated by Monte Carlo with the closed
   form is about `d/63` in the regime, so the covering lemma is loose by a
   constant only. It matches the Gaussian heuristic
   `Var log LR ~ k beta^2 4^(l-1)/3`.
4. **Theorem U, measured.**
   - `E_L max_R w(R|L)` approaches `1/(2^l - 1)`, with the `l = 3` values given
     above. At `l = 4` it is `0.1979, 0.0691, 0.0667` at `k = 2^6, 2^18, 2^30`,
     against `1/15 = 0.0667`.
   - The inequality `E_L TV(w(.|L), u_L) <= 2 TV(P0, Q)` holds at every tested
     point.
5. **Theorem W, measured.** The window is `q = 1`, `k = k_A(l)`:

   | `l` | `log2 k_A` | `log2 k_T` | `log2 k_0` | lower bound | MC `TV(P0,Q)` |
   |---|---|---|---|---|---|
   | 18 | 31.17 | 30.42 | 79.22 | 0.531 | 0.796 |
   | 20 | 34.16 | 34.42 | 83.26 | 0.748 | 0.831 |
   | 25 | 41.61 | 44.42 | 93.34 | 0.930 | 0.930 |
   | 30 | 49.02 | 54.42 | 103.41 | 0.965 | 0.965 |
   | 35 | 56.41 | 64.42 | 113.47 | 0.974 | 0.974 |

   Here `k_0` is the least `k` with `SD* <= 10^(-5)`. The lower bound at `k_T`
   is `>= 0.708` for every `l` from 20 to 35. The Monte Carlo estimate agrees
   with the lower bound from `l = 25` on, so there the bound is tight to three
   digits.

## Not covered

* **The truth of `T2`.** Rigidity itself may still hold in the window, through
  a proof that is not a transfer from a transitive test, for instance a direct
  spectral argument for the smoothed down-up walk. Theorem W kills only
  transfers.
* **Advice dimension `q >= 2`.** For `l >= 43`, admissibility already implies
  `SD* <= 10^(-5)` (Corollary S3 of
  `near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp`). There no
  window exists and Corollary N covers every admissible point. Two cases are
  not treated here: `q >= 2` with `l < 43`, and `k` between `k_T` and `k_0`
  for any `q`.
* **The per-A-vertex spread inside the window.** There the conditional seed law
  given `L` is heuristically still spread over about `2^l 4^(-m)` hyperplanes,
  so Proposition 4 probably fails there too. That is not proved.
* **The chi-squared form.** `(1 + beta^2 (a(1 + 2^(2-l))/3 - 1))^k - 1` is
  derived from the closed form but is not made rigorous. It is used only as a
  numerical cross-check.
