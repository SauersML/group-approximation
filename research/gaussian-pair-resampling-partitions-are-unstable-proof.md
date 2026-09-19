---
rg: 2
id: gaussian-pair-resampling-partitions-are-unstable-proof
kind: route
title: Power the pair-resampling walk 40 times, write the power as an average of Mehler operators of products of matching projections, get strict contraction on 1-perp from expansion of the 40 matchings, and apply Nelson on the fibres of the frame sum
target: gaussian-pair-resampling-partitions-are-unstable
requires: []
artifacts:
  - experiments/gaussian-pair-sum-universe-2026-09-17/check_gaussian_universe.py
---

Notation as in the target. All operators act on `L^2(gamma)`. Rescaling the
rows does not change any conditional expectation, so the rows are standard.
`N = 2n` is the number of labels, and `1` is the all-ones vector of `R^N`.

## Step 1: powering

Each `T_P` is an orthogonal projection, so `T = E_P T_P` is self-adjoint with
spectrum in `[0, 1]`. Let `mu_f` be the spectral measure of `f`, of mass
`||f||^2`. Holder on `[0,1]` gives
`<f, T f> = int lambda dmu_f <= (int lambda^j dmu_f)^(1/j) ||f||^(2(1-1/j))`.
Sum over `a` and apply Holder to the sum:

```text
Stab_T(rho) <= ( sum_a <rho_a, T^j rho_a> )^(1/j) ( sum_a ||rho_a||^2 )^(1 - 1/j)
            <= Stab_(T^j)(rho)^(1/j),
```

since `sum_a ||rho_a||^2 <= sum_a E rho_a = 1` (as `0 <= rho_a <= 1`).
With `P_1, ..., P_j` i.i.d. uniform, `T^j = E T_(P_1) T_(P_2) ... T_(P_j)`.

## Step 2: Mehler form

For a contraction `D` of `R^N` put
`M_D f(x) = E_(x') f((D (x) I) x + ((I - D D^T)^(1/2) (x) I) x')`, with `x'`
an independent copy of `G`. Then:

* `M_D` preserves `gamma` (the covariance is `D D^T + I - D D^T = I`), so by
  Jensen it is a contraction on `L^2(gamma)`;
* `M_(D_1) M_(D_2) = M_(D_2 D_1)`. Indeed the noise covariance of the
  composition is `D_2 (I - D_1 D_1^T) D_2^T + I - D_2 D_2^T = I - (D_2 D_1)(D_2 D_1)^T`;
* `T_P = M_(Pi_P)`, because `G = Pi_P G + (I - Pi_P) G` with independent
  summands, and conditioning on the first resamples the second.

Hence `T_(P_1) ... T_(P_j) = M_D` with `D = Pi_(P_j) ... Pi_(P_1)`. The
artifact checks the covariance identity numerically.

**Fibres.** Each `Pi_P` is symmetric and fixes `1`, so `D` and `D^T` fix `1`
and preserve `1-perp`. Write `x = (u, w)` with `u` the `span(1) (x) R^d`
coordinate (`u = s / sqrt N`) and `w` the `1-perp (x) R^d` coordinate; under
`gamma` they are independent standard Gaussians. Then `D = 1 (+) D'`,
`I - D D^T = 0 (+) (I - D' D'^T)`, and

`M_D f(u, w) = (M_(D') f(u, .))(w)`.

So `M_D` acts fibre by fibre in `u`, and on the fibre it is `M_(D')`.

## Step 3: contraction from expansion

**Lemma N.** Let `Pi_1, ..., Pi_j` be orthogonal projections of `R^N` with
`Pi_i = (projection onto vectors constant on the pairs of a perfect matching P_i)`,
let `H` be the multigraph union of the `P_i`, and `L_H` its Laplacian. For unit
`x` in `1-perp`, `||Pi_j ... Pi_1 x||^2 <= 1 - lambda_2(L_H)/(2 j^2)`.

*Proof.* Put `x_0 = x`, `x_i = Pi_i x_(i-1)` and
`delta_i = ||x_(i-1) - x_i|| = ||(I - Pi_i) x_(i-1)||`. By Pythagoras,
`1 - ||x_j||^2 = sum_i delta_i^2`. Also
`||(I - Pi_i) x|| <= delta_i + ||x - x_(i-1)|| <= sum_(t <= i) delta_t`, so
`||(I - Pi_i) x||^2 <= j sum_t delta_t^2 = j (1 - ||x_j||^2)`. For a matching,
`sum_({a,a'} in P) (x_a - x_a')^2 = 2 ||(I - Pi_P) x||^2`. So

`lambda_2(L_H) <= x^T L_H x = 2 sum_i ||(I - Pi_i) x||^2 <= 2 j^2 (1 - ||x_j||^2)`. QED.

**Cheeger, with proof.** Let `h(H) = min_(1 <= |S| <= n) e_H(S, S^c)/|S|`.
Then `lambda_2(L_H) >= h(H)^2/(2j)`. Take an eigenvector `f` of `lambda_2`,
orthogonal to `1`; replacing `f` by `-f` if needed, `|{f > 0}| <= n`. Let
`g = max(f, 0)`, which is nonzero. For `v` with `f_v > 0`,
`(L g)_v <= (L f)_v = lambda_2 f_v`, since `g >= f` off `v`. So
`sum_(edges) (g_u - g_v)^2 = <g, L g> <= lambda_2 ||g||^2`. Every level set
`{g^2 > t}`, `t >= 0`, has at most `n` vertices, so by the co-area formula
`sum_(edges) |g_u^2 - g_v^2| >= h ||g||^2`. By Cauchy--Schwarz and
`(g_u + g_v)^2 <= 2 g_u^2 + 2 g_v^2`, the left side is at most
`(lambda_2 ||g||^2)^(1/2) (2 j ||g||^2)^(1/2)`. Hence `h <= sqrt(2 j lambda_2)`.

**Consequence.** If `h(H) >= h0`, then
`r := ||D'|| <= r0 = (1 - h0^2/(4 j^3))^(1/2) < 1`.

**Nelson on the fibre.** Suppose `r > 0` (the case `r = 0` is immediate) and
put `E = D'/r`, so `||E|| <= 1`. By the composition rule,
`M_(D') = M_(sqrt r I) M_E M_(sqrt r I)`. Here `M_(sqrt r I)` is the
Ornstein--Uhlenbeck operator `P_t` with `e^(-t) = sqrt r`, which is
self-adjoint. So for `f` on the fibre

`<f, M_(D') f> = <P_t f, M_E P_t f> <= ||P_t f||_2^2 <= ||f||_(1+r)^2`,

by Nelson's hypercontractive inequality `||P_t f||_2 <= ||f||_p` for
`p = 1 + e^(-2t) = 1 + r`. For `f = rho_a(u, .)`, with values in `[0,1]` and
fibre mean `E[rho_a | s] = 1/N`,
`||f||_(1+r)^2 <= (E f)^(2/(1+r)) = N^(-2/(1+r))`. Summing over the `N` labels
and averaging over `u`:

`sum_a <rho_a, M_D rho_a> <= N^(1 - 2/(1+r)) = N^(-(1-r)/(1+r)) <= N^(-kappa)`,

with `(1-r)/(1+r) >= (1 - r0^2)/4 = h0^2/(16 j^3) = kappa`.

## Step 4: expansion is typical (Lemma E)

Let `P` be a uniform perfect matching of `[N]` and `|S| = s <= n`.

* **Small sets.** If `e_P(S) < h0 s`, then `S` contains at least
  `m0 = ceil(s(1-h0)/2)` pairs of `P`. There are at most `(s^2/2)^m0 / m0!`
  sets of `m0` disjoint pairs inside `S`. A given one lies in `P` with
  probability `prod_(i < m0) 1/(N - 2i - 1) <= n^(-m0)` (as `m0 <= n/2`). So
  `Pr[e_P(S) < h0 s] <= (e s^2/(2 n m0))^m0 <= (e x/(1-h0))^(s(1-h0)/2)`,
  where `x = s/n` and `e x/(1-h0) <= 1` for `x <= 1/4`.
* **Large sets.** Expose `P` by repeatedly matching the least unmatched vertex
  of `S` to a uniform unmatched vertex. Do `k = ceil(s/2)` steps; each uses at
  most two vertices of `S`, so this is possible. Before step `i+1` at most `i`
  vertices of `S^c` are used, so the step crosses with conditional
  probability at least `(N - s - i)/(N - 2i - 1) >= 1 - 3s/(2N) >= 1/4`.
  Crossing steps give distinct crossing pairs, so `e_P(S)` stochastically
  dominates `Bin(k, 1/4)`. With `h0 s <= 2 h0 k` and Chernoff,
  `Pr[e_P(S) < h0 s] <= exp(-(s/2) D)`, `D = KL(2 h0 || 1/4) >= 0.2116`.

For `j` independent matchings, `e_H(S) < h0 s` forces `e_(P_i)(S) < h0 s` for
every `i`. With `C(N, s) <= (2e/x)^s`, a union bound gives

```text
Pr[h(H) < h0] <= eps_n := sum_(2 <= s <= n/4) [ (2e/x) (e x/(1-h0))^(j(1-h0)/2) ]^s
                        + sum_(n/4 < s <= n) [ 8e exp(-j D/2) ]^s.
```

(`s = 1` never fails: a single vertex always has a crossing pair.) At
`j = 40`, `h0 = 1/100` the first base is increasing in `x` and at most
`0.0126` at `x = 1/4`, and it is at most `2.7e9 x^18.8`. The second base is
`0.316`. So `eps_n <= O(n^(-35)) + n 0.0126^(sqrt n) + n 0.316^(n/4) -> 0`.
The artifact evaluates `eps_n` exactly (`< 1.5e-13` at `n = 100`) and checks
both tail bounds against the exact crossing law for `n <= 100`.

## Conclusion

On `h(H) >= h0`, Step 3 gives `sum_a <rho_a, M_D rho_a> <= N^(-kappa)`. On
the complement, `|sum_a <rho_a, M_D rho_a>| <= sum_a ||rho_a||^2 <= 1`.
Averaging over the matchings, `Stab_(T^40)(rho) <= N^(-kappa) + eps_n`, and
Step 1 finishes. Only balance was used, not equivariance.
