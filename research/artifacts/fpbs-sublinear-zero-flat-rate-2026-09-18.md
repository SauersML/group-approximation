# Zero-free continuation is exactly the flat-rate hole; the tree calibration (2026-09-18)

Lane: swarm-0917-w8-w8-bs-last1, the last-mile lane toward
`fpbs-benjamini-schramm-universal`.

New nodes:

- `fpbs-sublinear-zero-interpolant-iff-flat-rate` (established), with route
  `-proof`;
- `fpbs-tree-connection-zeros-linear-past-flat-edge` (established), with route
  `-proof`;
- the hole `fpbs-flat-walk-rate-past-pc-universal` [F] (open), with routes
  `fpbs-flat-rate-route` (to BS), `fpbs-flat-rate-from-fourier-algebra` and
  `fpbs-flat-rate-from-zero-free-polynomials`.

## 1. What was asked and what was found

The route `fpbs-zero-free-connectivity-route` to BS is missing one
prerequisite, (ZG) (`fpbs-connectivity-polynomials-zero-free-around-criticality`).
Its bridge `fpbs-zero-free-connectivity-gives-flat-rate` was refereed and
reproved in this lane; see `fpbs-zero-free-flat-rate-referee-2026-09-18.md`.
The question was how close (ZG) is to being provable. Three findings follow.

1. **Class kill.** (ZG) can be weakened a long way and still give the
   flat rate `lambda(p_+) = rho`:
   - analytic interpolants in place of polynomials;
   - `o(n)` zeros in place of none;
   - a subsequence of `n`;
   - domination only at one point `p_+`.

   In this weakened form it becomes *equivalent* to the flat rate. The
   constant family `F_n = rho^n` witnesses the converse. So complex analysis
   of interpolants carries no information beyond [F]. The content of (ZG) lies
   entirely in naming the polynomials `a_(n,R)`, `R >= n`.
2. **Sharpness.** `o(n)` zeros cannot be relaxed to `O(n)`. Shifted Chebyshev
   polynomials `rho^n T_n((z-c)/s - i n^(-1/2))` meet (E) and (G), have `n`
   zeros, and grow at rate `rho e^(g)` off the interval.
3. **Calibration (changes belief).** On `T_3`, (ZG) as proposed on
   `|z-1/2| < 1/4` is false. That domain contains `0.74 > p_lambda = 0.7071`,
   and past `p_lambda` the tree rate is `phi(p) > rho`. So linearly many zeros
   must enter a compact subset of the disc. The 2026-09-17 zero-free scan
   (`n <= 200`) is a finite-size effect. The predicted count is `0.00099 n`,
   and the first pair of zeros inside the disc appears between `n = 1000` and
   `n = 2000`. The zero of `a_2000` at `0.7325276 + 0.0588817 i` is confirmed
   in exact arithmetic.

## 2. The equivalence theorem (summary)

For `p_+` in `(p_c,1)` the following are equivalent:

- (1) `lambda(p_+) = rho`;
- (2) `a_n(p_+) <= rho^n` for all `n`;
- (3) there is an interpolant family with (E), (P), (G) and (Z) on a symmetric
  simply connected domain.

The steps:

- *(1) <=> (2).* `a_(n+m) >= a_n a_m`, by Harris-FKG, left invariance and
  independence of the walk increments. Fekete then gives
  `lambda = sup a_n^(1/n)`. Hence (1) and (2) are equivalent.
- *Lower bound.* `a_n >= P(X_n = o)`, or `p P(X_(n-1) = o)` for odd `n`, gives
  `lambda >= rho`.
- *(3) => (1).*
  - Divide out the `o(n)` zeros.
  - The `n`-th root `h_n` of the zero-free quotient is bounded by the
    mean-value property; the circle average of `log|w - zeta|` is
    `log max(r, |z - zeta|)`.
  - Montel gives limits `g`.
  - On the real interval, `|g| >= rho` pointwise. The integrated bound
    `int_J log|x - zeta| dx >= -C_J` gives `int_J log|g| <= |J| log rho`.
    So `|g| = rho` on `J`.
  - `g` times its Schwarz reflection equals `rho^2` on `J`, and hence on the
    domain.
  - At `p_+`, `limsup a_n^(1/n) <= rho`.
- *Corollaries.*
  - (C2): ZG with `o(n)` zeros on a symmetric domain suffices.
  - (C4): if `lambda(p_+) > rho`, some compact subset carries at least `c n`
    zeros for all large `n`, by a diagonal argument.

## 3. The tree computation

On `T_d`, `a_n(z) = E z^(|X_n|)`, and the distance chain gives the one-step
identity

    a_(t+1) = phi a_t + (z - phi) r_t,    phi(z) = ((d-1) z + 1/z)/d,  r_t = P(X_t = o).

- For `p <= p_lambda = (d-1)^(-1/2)`, `f(k) = p_lambda^k` satisfies
  `Pf <= rho f`. So `a_n(p) <= rho^n`, and the rate is flat.
- For every real `p` with `phi(p) > rho`,
  `a_n(p) = C(p) phi^n + O(rho^n)`, where
  `C(p) = 1 + (p - phi) G(1/phi)/phi`.
- `C = 0` on `(0, p_lambda)`, by the flat bound.
- `phi(p) = phi(w)` for `w = 1/((d-1)p)`, so for `p > p_lambda`,
  `C(p) = (p - w) G(1/phi)/phi > 0`.

So `lambda(p) = phi(p) > rho` on `(p_lambda, 1)`. The flat edge is
`p_F = p_lambda = p_2 = p_A`, strictly between `p_c = 1/(d-1)` and `p_u = 1`.

**Where the zeros sit (heuristic, supported by the table).**

- The two competing terms are `C phi^n` and a tail of size about
  `rho^n n^(-3/2)`. Their moduli balance on
  `Gamma = {|phi| = rho, |z| >= p_lambda}`, at distance `O(log n / n)`.
- With `z = p_lambda u` and `u + 1/u = 2 e^(i alpha)`, `|u| >= 1`, we have
  `phi = rho e^(i alpha)` on `Gamma`.
- The curve leaves `p_lambda` at +-45 degrees, and `phi^n` winds once per
  `2 pi / n` of `alpha`.
- Prediction: `n alpha_max / pi` zeros in a symmetric disc. Here `alpha_max` is
  the largest `alpha` on `Gamma` inside the disc.

## 4. Numerics

Script: `experiments/fpbs-zero-count-flat-rate-2026-09-17/tree_zero_count_linear.py`
(numpy). Run it as

    python3 experiments/fpbs-zero-count-flat-rate-2026-09-17/tree_zero_count_linear.py 200 1000 2000 4000 8000

The method:

- Zeros are counted by the argument principle on circles with `40 n` points.
- `rho^(-n) a_n` is evaluated through the head identity, or the tail identity
  `a_n = -(z - phi) sum_(j>=n) r_j phi^(n-1-j)`.
  - The tail is used in the inner region `|z| < p_lambda`,
    `|phi| > rho (1 + 15/n)`. There `C = 0` by analytic continuation: the
    region is connected, being the Joukowski image of `{|w| > 2}` minus
    `[-2,2]`.
- Return probabilities come from the Doob-transformed distance chain, scaled
  by `rho^(-j)`.
- At `n = 60` the evaluator agrees with direct evaluation to `3e-14`.

A bug fix during the run. An unscaled first version stored `r_j` directly.
Those values become subnormal past `j` of about 12000. The tail sum multiplies
them by `|phi|^(-k)` with `k` up to `4n`. At `n = 4000` this gave garbage
counts (for example 140 zeros in `|z-1/2| < 0.15`). The scaled version
replaces it; the `n <= 2000` rows are unchanged.

Zeros of `a_n` on `T_3`:

| n | \|z-.5\|<.25 | \|z-.5\|<.24 | \|z-.5\|<.15 | \|z-.7071\|<.05 | \|z-.7071\|<.10 |
|---|---|---|---|---|---|
| 200 | 0 | 0 | 0 | 0 | 0 |
| 1000 | 0 | 0 | 0 | 0 | 2 |
| 2000 | 2 | 2 | 0 | 0 | 4 |
| 4000 | 4 | 2 | 0 | 2 | 10 |
| 8000 | 8 | 6 | 0 | 4 | 22 |
| predicted slope per n | 0.00099 | 0.00060 | 0 | 0.00076 | 0.00289 |
| predicted at n = 8000 | 7.9 | 4.8 | 0 | 6.1 | 23.2 |

The counts are even, which is conjugate symmetry. In the scanned disc they
double with `n` (0, 2, 4, 8 at `n` = 1000, 2000, 4000, 8000), which is linear
growth at the predicted slope. The other discs track their slopes within one
or two pairs; near `p_lambda` the finite-`n` offset of the zeros from `Gamma`
matters more. The count in the inner disc `|z-1/2| < 0.15` stays 0, as
predicted: the whole of that disc lies in `|z| < p_lambda`, where
`a_n = O(rho^n)` has no dominant competing term.

**Exact confirmation at n = 2000.**
`experiments/fpbs-zero-count-flat-rate-2026-09-17/exact_zero_check.py` evaluates
`3^n a_n(z)` with Python integers at 9-digit Gaussian rationals.

| z | \|z-1/2\| | log10 \|a_2000(z)\| | log10 max_k P_k \|z\|^k |
|---|---|---|---|
| 0.732527580 + 0.058881712 i (Newton root, rounded) | 0.23987 | -60.68 | -52.88 |
| 0.7325 + 0.0589 i | 0.23990 | -55.76 | -52.89 |
| 0.73 + 0.06 i | | -53.95 | -53.02 |

A drop of five orders of magnitude over a distance ratio of about `5 x 10^4`
is what a simple zero gives. With its conjugate, this is the pair the
argument principle counts in `|z-1/2| < 0.24` at `n = 2000`.

## 5. Consequences for the graph

- `fpbs-zero-free-connectivity-route` is still missing one prerequisite, (ZG).
  Its tree evidence is now corrected: any universal (ZG) must use domains
  whose real trace stops below `p_F`. On trees that is `(d-1)^(-1/2)`.
- The new hole [F] sits under both the ZG route and the [A] route. The route
  `fpbs-flat-rate-route` reduces BS to [F] alone, plus established nodes.
- [F] is implied by [A], and so by `p_c < p_2` and by `p_c < p_(2->2)`. It
  implies (IS). No separating example is known in either direction. Its
  annealed analogue is false on the Angel--Hutchcroft graph, so any proof must
  be Cayley-specific.
- Question: does [F] imply [A], that is, is `p_F = p_A` on every Cayley graph?
  It does on trees.
