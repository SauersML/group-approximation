---
rg: 2
id: thompson-f-norm-bound-from-forest-renewal-test-vector
kind: claim
title: Simple random walk on Thompson's group F has Markov operator norm above 0.9397 (explicit forest-stack test vector), outside the published 2.53±0.03 cogrowth estimate
distinct_from:
  thompson-f-norm-bound-from-epg-32-term-moments: that certifies ||P|| > 0.910677 from the 32 published cogrowth terms, about the optimum of the moment route; this certifies ||P|| > 0.9397 from no moment data at all, by one explicit nonnegative test vector on a forest window with more than 10^18000 states, evaluated exactly by a renewal DP.
  thompson-f-norm-bound-from-hhr-exact-moments: that certifies ||P|| > 0.901532 from 25 moments.
  thompson-f-random-walk-norm-certified-lower-bound: that certifies ||P|| > 0.880541 from counts to length 30.
  thompson-f-moment-data-cannot-certify-nonamenability: that shows no finite list of counts proves ||P|| < 1; this is a lower bound only and says nothing about amenability.
artifacts:
  - experiments/thompson-f-norm-ansatz-2026-09-17/certify_window.py
  - experiments/thompson-f-norm-ansatz-2026-09-17/params_N80.json
  - experiments/thompson-f-norm-ansatz-2026-09-17/certificate_N80_n30000.json
  - experiments/thompson-f-norm-ansatz-2026-09-17/certify_N80_n30000.out
  - experiments/thompson-f-norm-ansatz-2026-09-17/certify_N80_n30000_json.out
  - experiments/thompson-f-norm-ansatz-2026-09-17/params_N40.json
  - experiments/thompson-f-norm-ansatz-2026-09-17/certificate_N40_n20000.json
  - experiments/thompson-f-norm-ansatz-2026-09-17/certify_N40_n20000_json.out
  - experiments/thompson-f-norm-ansatz-2026-09-17/model_check.py
  - experiments/thompson-f-norm-ansatz-2026-09-17/model_check.out
  - experiments/thompson-f-norm-ansatz-2026-09-17/split_ansatz.py
  - experiments/thompson-f-norm-ansatz-2026-09-17/iid_ansatz.py
  - experiments/thompson-f-norm-ansatz-2026-09-17/size_ansatz.py
  - experiments/thompson-f-norm-ansatz-2026-09-17/window_dp.py
  - experiments/thompson-f-norm-ansatz-2026-09-17/window_dp_brute.out
---

**ESTABLISHED (computer-assisted, exact rational arithmetic).** Let
`P = (x_0 + x_0^{-1} + x_1 + x_1^{-1})/4` act on `l^2(F)`. Then

    ||P|| > 9397/10000 = 0.9397,

and more precisely `||x_0 + x_0^{-1} + x_1 + x_1^{-1}|| >= a/b` with

    a = 522122018478774136254787217627162562318348622267386
    b = 138903651076739081275986180908611042223851082828941      (a/(4b) = 0.939719753...).

Consequences:
- **Cogrowth rate.** `mu = 16 ||P||^2 > 16 * 0.9397^2 = 14.12857744`. This exceeds EP-G's
  *conditional* bound `13.706` (which assumes monotone recurrence coefficients) as an unconditional
  statement.
- **Reduced cogrowth.** Grigorchuk's cogrowth formula is `4||P|| = alpha + 3/alpha`, where
  `alpha > sqrt 3` is the growth rate of freely reduced trivial words (ERJvR's "cogrowth", with
  amenable value `3`). It gives `alpha > 2.6088`.
- **Density.** The Cheeger density corollary (step 6 of
  `thompson-f-norm-bound-from-epg-32-term-moments-proof`, which applies to any lower bound `r`)
  gives finite sets of average inner degree arbitrarily close to at least
  `4 - 4 sqrt(1 - 0.9397^2) > 2.632`.

**Belief change: a published numerical estimate is wrong.** Elder, Rechnitzer and Janse van
Rensburg (arXiv:1312.5722, `rand_dec20.tex` l.1499–1550, quoted verbatim in
`research/artifacts/thompson-f-cogrowth-literature-pins-2026-09-13.md`) estimate "cogrowths of
approximately 2.53±0.03" for this presentation. Their upper end `alpha = 2.56` corresponds to
`||P|| = 0.93297`. The certified `alpha > 2.6088` lies outside the whole stated interval.

The authors add that "these estimates do not constitute a proof". The HHR suggestion
`||A|| ≈ 3.87` (`||P|| ≈ 0.9675`) and the EP-G extrapolation `mu ≈ 15.0` (`||P|| ≈ 0.968`)
remain consistent with the bound and uncertified. Any argument that leaned on "`||P|| ≈ 0.929`,
visibly below 1" loses its numerical support: the gap to amenability is at most `0.0603`, not
`0.071`.

**Method (not moments).** The certificate is one explicit nonnegative function `f` on the
pointed forests with `n = 30000` leaves. They form a finite subset `S_n` of `F` whose forest moves
are Cayley edges (route steps 1–2).
- *Bulk trees:* `x(T) = phi(|L|,|R|) x(L) x(R)`.
- *Pointer tree:* `y(T) = g(|L|,|R|) y(L) x(R)`.
- *The vector:* `f = y(pointer tree) * prod x(other trees)`. Trees with more than `N = 80` leaves
  get weight `0`.
- *Parameters:* the 6320 split weights are dyadic rationals over `2^24`, stored in `params_N80.json`.
- *Evaluation:* `<f, A f>` and `<f, f>` come from an exact renewal recursion in fixed point with
  outward rounding. `|S_n| >= Cat(n-1) > 10^18000`, and the DP never enumerates it.

The moment route's optimum is `0.910677` (32 terms), which this beats by `0.029`. The previous
node's Attempts recorded "No explicit window test vector beats `0.9107` within reach" for
Dirichlet eigenvectors of small windows. The product-form vector avoids that obstruction because
it lives on huge windows, where the `1/n` boundary loss is negligible.

A second, independent instance at `N = 40, n = 20000` (`params_N40.json`) certifies
`||A|| >= 979051926869845066870645505868521958056889377604163/263553902935005215428061453500325780059153935835220`,
that is `||P|| > 0.9287`.

**Scope.** Lower bound only. A lower bound below `1` cannot decide amenability, and `||P|| = 1`
(amenable) is consistent with everything here. This node moves the certified floor and refutes a
numerical estimate. It does not move the amenability question in either direction.

Proof route: `thompson-f-norm-bound-from-forest-renewal-test-vector-proof`.

## Attempts

- **Ansatz families (floating point, scouting).** The families are nested. All Rayleigh
  quotients are `/4`, in the `n -> infinity` limit.
  - Full-shape i.i.d. optimum over all trees up to `N` leaves (`iid_ansatz.py`):
    - `0.8340` (N=5), `0.8617` (7), `0.8777` (9), `0.8835` (10);
    - its optimiser has the multiplicative split form above to machine precision.
  - Size-only weights (`size_ansatz.py`, `x(T)` depending on `|T|` only):
    `0.92005` (N=160), `0.92272` (320), `0.92438` (640).
  - Split form (`split_ansatz.py`):
    - `0.87771` (9, equal to the full i.i.d. optimum), `0.91179` (20), `0.92897` (40), `0.94002` (80);
    - mean tree size under the bulk weights: `7.45` at N=40, `12.57` at N=80.

  The increments are `0.0171`, `0.0110` per doubling and still decaying slowly, so the family's
  supremum is above `0.95` if the trend holds. It is not established whether this family reaches
  `1`. Heuristically, reaching `1` needs the bulk-tree size distribution to become heavy-tailed,
  which is the shape Følner forests would have if `F` were amenable. So the `N -> infinity`
  behaviour of the split optimum is a computable proxy for the question, though it is not
  equivalent to it. OPEN.
- **Finite-window convergence.** At fixed parameters the window quotient converges like `1/n`.
  - Size-only at N=160: `0.91873` (`n = 10^4`) and `0.91992` (`10^5`), against the limit `0.92005`.
  - Certificates: `0.928702` at `N = 40, n = 20000` (limit `0.928967`), and `0.939720` at
    `N = 80, n = 30000` (limit `0.940020`).
