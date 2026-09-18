---
rg: 2
id: fpbs-tree-connection-zeros-linear-past-flat-edge-proof
kind: route
title: Solve the distance chain exactly through the one-step identity a_(t+1)=phi a_t+(z-phi)r_t, read off lambda=phi past p_lambda, and apply the forced-zeros corollary
target: fpbs-tree-connection-zeros-linear-past-flat-edge
requires:
  - fpbs-sublinear-zero-interpolant-iff-flat-rate
  - fpbs-zero-free-connectivity-gives-flat-rate
artifacts:
  - research/artifacts/fpbs-sublinear-zero-flat-rate-2026-09-18.md
  - experiments/fpbs-zero-count-flat-rate-2026-09-17/exact_zero_check.py
---

Notation is that of the target. Write `Y_t = |X_t|` and `r_t = P(Y_t = 0)`.

**Imports.**

- (K) `r_t <= rho^t` for all `t`, since `r_t = <P^t delta_o, delta_o>` and
  `||P|| = rho`. Also `r_(2m)^(1/(2m)) -> rho`, with
  `rho(T_d) = 2(d-1)^(1/2)/d`. This is Kesten, Trans. AMS 92 (1959); see
  Woess, *Random walks on infinite graphs and groups*, Chapter I. The limit
  exists by Fekete, since `r_(2m+2k) >= r_(2m) r_(2k)`, and it equals the norm
  for a symmetric operator. `r_t = 0` for odd `t`.
- Corollary (C4) of `fpbs-sublinear-zero-interpolant-iff-flat-rate` (proved
  in its route), used in 2.
- Theorem (a) of `fpbs-zero-free-connectivity-gives-flat-rate`, used in 3.

**Step 1: the one-step identity.** `Y` is the Markov chain on
`{0,1,2,...}` that goes `0 -> 1` with probability 1 and `k -> k+1`, `k -> k-1`
with probabilities `(d-1)/d` and `1/d` for `k >= 1`. For `f(k) = z^k`,
`E[f(Y_(t+1)) | Y_t = k] = phi(z) z^k` if `k >= 1`, and `= z` if `k = 0`.
Hence

    a_(t+1)(z) = phi(z) a_t(z) + (z - phi(z)) r_t,    a_0 = 1,

and by induction, for `z != 0`,

    a_n(z) = phi^n [1 + (z - phi) sum_(t<n) r_t phi^(-1-t)].      (1)

**Step 2: the flat side.** Let `0 < p <= p_lambda`. Put
`f(k) = p_lambda^k`. For `k >= 1`, `Pf(k) = phi(p_lambda) f(k) = rho f(k)`, and
`Pf(0) = p_lambda <= rho f(0)`, because `p_lambda <= rho` is equivalent to
`d <= 2(d-1)`. So `Pf <= rho f` pointwise, `P^n f <= rho^n f`, and
`a_n(p) <= a_n(p_lambda) = (P^n f)(0) <= rho^n`. Together with
`a_n(p) >= r_n` (even `n`) and `>= p r_(n-1)` (odd `n`), (K) gives
`lambda(p) = rho`.

**Step 3: the constant C.** For real `p > 0` with `phi(p) > rho`, the series
`G(1/phi) = sum_t r_t phi^(-t)` converges by (K). Put
`C(p) = 1 + (p - phi) G(1/phi)/phi`. By (1),

    a_n(p) = C(p) phi^n - (p - phi) sum_(t>=n) r_t phi^(n-1-t),      (2)

and by (K) the last sum is at most `rho^n / (phi - rho)` in absolute value.
So `a_n(p) = C(p) phi^n + O(rho^n)`.

- If `0 < w < p_lambda`, then `phi(w) > rho` (by AM-GM,
  `phi(x) >= rho` with equality only at `x = p_lambda`). Step 2 gives
  `a_n(w) <= rho^n`, so `C(w) phi(w)^n = O(rho^n)`, and `C(w) = 0`.
- For `p` in `(p_lambda, 1)` put `w = 1/((d-1)p)`, which lies in
  `(0, p_lambda)`. Then `(d-1)w + 1/w = 1/p + (d-1)p`, so `phi(w) = phi(p)`,
  and `C(p) = C(p) - C(w) = (p - w) G(1/phi(p))/phi(p) > 0`.

So `lambda(p) = phi(p) > rho` on `(p_lambda, 1)`. This proves 1.

**Step 4: linear zeros (part 2).** `U` is open, so it contains a compact
nondegenerate interval `I` in `(0, p_lambda)`. Take `F_n = a_n` for all `n`.

- (E) holds on `I` by Step 2 and (K), uniformly on `I`.
- (P) holds with equality.
- (G): `|a_n(z)| <= sum_k P(Y_n = k) |z|^k <= max(1,|z|)^n`.
- `lambda(p_+) = phi(p_+) > rho` by Step 3.

Corollary (C4) gives a compact `K` in `U` and `c > 0` with at least `c n`
zeros of `a_n` in `K` for all large `n`.

**Step 5: ZG on trees (part 3).** `a_(n,R) = a_n` for `R >= n`. If (ZG) holds
with exact zero-freeness, then theorem (a) of the zero-free claim gives
`lambda = rho` on `I_+`, so `I_+` lies in `(0, p_lambda]` by Step 3. If (ZG)
holds with `o(n)` zeros on compacts of a symmetric `U`, then `U` contains
`I_-`, a subset of `(0, p_c]` and so of `(0, p_lambda)`. By Step 4, `U`
contains no point of `(p_lambda, 1)`.

**Step 6: the scanned disc (part 4).** `D = {|z - 1/2| < 1/4}` is convex and
symmetric, and contains `(0.3, 0.7)` and `0.74 > p_lambda = 2^(-1/2)`. Step 4
applies. The zero of `a_2000`:

- It was located by Newton's method on the scaled head/tail evaluator of
  `tree_zero_count_linear.py`.
- It was confirmed by `exact_zero_check.py`, which evaluates
  `3^n a_n(z)` in exact integer arithmetic at 9-digit Gaussian rationals.
- At `z = 0.732527580 + 0.058881712 i`, `log10 |a_2000| = -60.68`.
- At `0.7325 + 0.0589 i`, a distance of `3.3e-5`, it is `-55.76`.
- The no-cancellation scale `max_k P(Y_n=k)|z|^k` is `10^(-52.9)`.
- The five orders of magnitude drop over a factor of about `5 x 10^4` in
  distance is what a simple zero within the rounding radius `7e-10` gives.
- The argument-principle count on `|z - 1/2| = 0.24` is 2 at `n = 2000`,
  matching the pair.

Parts 1 to 3 do not depend on the numerics. QED.
