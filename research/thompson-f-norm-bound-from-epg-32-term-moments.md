---
rg: 2
id: thompson-f-norm-bound-from-epg-32-term-moments
kind: claim
title: Simple random walk on Thompson's group F has Markov operator norm above 0.9106 (exact certificate on the 32 published cogrowth terms)
distinct_from:
  thompson-f-norm-bound-from-hhr-exact-moments: that certifies ||P|| > 0.901532 from 25 moments (HHR table, words to length 48); this certifies ||P|| > 0.910677 from the 32 moments printed by Elvey Price and Guttmann (words to length 62), and reproduces the HHR certificates exactly as a consistency check.
  thompson-f-random-walk-norm-certified-lower-bound: that certifies ||P|| > 0.880541 from counts computed in this repository to length 30.
  thompson-f-moment-data-cannot-certify-nonamenability: that shows no finite list of counts proves ||P|| < 1; this is a lower bound only and says nothing about amenability.
artifacts:
  - experiments/thompson-f-cogrowth-2026-09-17/epg_certify.py
  - experiments/thompson-f-cogrowth-2026-09-17/epg_certify.json
  - experiments/thompson-f-cogrowth-2026-09-17/trend_analysis.py
  - experiments/thompson-f-cogrowth-2026-09-17/trend_analysis.json
  - experiments/thompson-f-cogrowth-2026-09-17/cogrowth_table.csv
  - experiments/thompson-f-cogrowth-2026-09-17/forest_window_scout.py
  - experiments/thompson-f-cogrowth-2026-09-17/forest_window_scout.json
---

**ESTABLISHED (computer-assisted, exact rational arithmetic on published data).** Let
`P = (x_0 + x_0^{-1} + x_1 + x_1^{-1})/4` act on `l^2(F)`. Then

    ||P|| > 910677/1000000 = 0.910677,

equivalently `||x_0 + x_0^{-1} + x_1 + x_1^{-1}||_{C*_r(F)} > 3.642708`, and the cogrowth rate
`mu = limsup c_n^{1/n} = 16 ||P||^2` satisfies `mu > 16 * 41466679/50000000 = 13.26933728`.

Consequence (same route, step 6): the Cayley graph of `F` with these generators contains finite
sets of average inner degree arbitrarily close to at least `4 - 4 sqrt(1 - 0.910677^2) > 2.3475`.

**Priority.** Not new as a number. A. Elvey Price and A. J. Guttmann, *Numerical studies of
Thompson's group F and related groups*, arXiv:1706.07571 (Internat. J. Algebra Comput.), arXiv source
`Group-growth23-6.tex`:
- abstract, l.42: "We have also given an improved algorithm for the coefficients of Thompson's
  group $F,$ giving 32 terms of the cogrowth series."
- l.481: "Using these we have computed the rigorous lower bound $b_{31}\approx13.269$ for the
  exponential growth rate of the cogrowth sequence of Thompson's group."

The value `16 theta = 13.26934` here matches their `b_31`. What this node adds to the graph: an
explicit rational witness vector that anyone can re-verify, a cross-check of the table against two
independent sources, and the move of the graph's best certified bound from `0.901532` to `0.910677`.

**Data.** `c_n` = number of words of length `2n` in `x_0^{+-1}, x_1^{+-1}` that are trivial in `F`,
`n = 0..31`, from the EP-G table "Terms in the cogrowth sequence of Thompson's group $F$"
(`Group-growth23-6.tex` l.296–333), embedded in `epg_certify.py` and re-parsed from the TeX.
- `n <= 15` agree exactly with this repository's own computation `experiments/thompson-f/out15.json`.
- `n = 16..24` agree exactly with the HHR Case 2 table (`experiments/thompson-f/hhr_certify.json`).
- `n = 25..31` are imported from EP-G only and were not recomputed (trust surface).
- All 32 terms satisfy `c_n <= binom(2n,n)^2` (the `Z^2` quotient count) and log-convexity of
  `c_n/16^n`, as moments of a measure must.

**Scope.** Lower bound only. EP-G's extrapolation `mu ≈ 15.0` (l.481) and their conditional bound
`13.706` (which assumes monotone recurrence coefficients) are not certified and not claimed.
Density comparison, not used by the proof: Belk–Brown marked-forest sets have average degree tending
to `7/2`, which gives only `||P|| >= 7/8` by the indicator Rayleigh quotient. Conversely step 6 turns
`0.910677` into density `2.3475` only. The two certified quantities are not comparable by these
inequalities; the Cheeger density bound would reach `3.5` only at `||P|| > 0.9922`.

Proof route: `thompson-f-norm-bound-from-epg-32-term-moments-proof`.

## Attempts

- **Extend the exact counts past `n = 31`.** Meet-in-the-middle needs the distribution of words of
  length `~n/2` over group elements. The support of the PL-map DP (`cogrowth_exact.py` style) is
  10,133,856 elements at radius 15 and grows by a factor of about `2.72` per step, so radius 16 is
  about `2.8e7` elements with multi-word counts. EP-G reached `n = 31` with a forest-diagram DFS.
  Going beyond needs about `1e13` element visits. Dies: resources (4 cores, 15 GB, a few hours), not
  mathematics. Each extra term would add about `0.001` to the bound, judging from the certified
  bounds `0.901532` at `N = 24` and `0.910677` at `N = 31`.
- **Dirichlet eigenvalues of finite forest-window sets as test vectors.** For any finite vertex set
  `S`, `lambda_max(A_S)/4 <= ||P||`. An integer Perron vector would be a certificate of a different
  kind from moments. `forest_window_scout.py` (floating point, scouting only; the forest-move model
  was not cross-checked against PL arithmetic) uses `S_n` = marked forests with `n` leaves, pointer
  anywhere:

  | n | \|S_n\| | avg inner degree | lambda/4 |
  |---|---------|------------------|----------|
  | 8 | 3432 | 2.333 | 0.75992 |
  | 9 | 11934 | 2.370 | 0.77791 |
  | 10 | 41990 | 2.400 | 0.79253 |
  | 11 | 149226 | 2.424 | 0.80466 |

  The increments are `≈ 1.46/n^2`, and `n^2 × increment` is still drifting up. The fit extrapolates
  to a limit of about `0.932`, but it would pass `0.910677` only at `n ≈ 68`. `|S_n|` grows by a
  factor of about `3.55` per step, so that set has more than `1e35` states.

  Height-bounded sets converge faster but to lower limits: height `<= 2` gives `0.7751` at `n = 14`
  (geometric-tail extrapolation `≈ 0.797`), and height `<= 3` gives `0.7972` at `n = 12` (`≈ 0.834`).

  Dies at: at every size this machine can reach, the Dirichlet eigenvalue is far below the moment
  bound. The window sets are Følner-like in the positive direction only, and their eigenvalue
  converges like `1/n`. The bound from `2n` moments improves geometrically in information, although
  slowly in value. No explicit window test vector beats `0.9107` within reach.
