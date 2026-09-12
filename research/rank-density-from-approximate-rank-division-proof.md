---
rg: 2
id: rank-density-from-approximate-rank-division-proof
kind: route
title: Riemann sums of spectral tails, then divide by L
target: rank-density-from-approximate-rank-division
requires: []
artifacts:
  - research/artifacts/toms-winter-rank-density-firewall-2026-09-11.md
---

**Layer-cake bound.**  Fix `tau` and let `mu` be the spectral measure of `a`
in the GNS representation of `tau`, a positive measure on `[0, K]` of total
mass `tau(1) = 1`.

- For `t >= 0`, `d_tau((a - t)_+) = lim_n tau((a-t)_+^(1/n)) = mu((t,K])`.
- `d_tau` is additive on direct sums.
- `tau(a) = integral_0^K mu((t,K]) dt`.
- The integrand is non-increasing in `t`, so the right-endpoint Riemann sum
  `(1/L) sum_(l=1..KL) mu((l/L,K])` lies between
  `integral - (1/L) mu((0,K])` and the integral.  Since `mu((0,K]) <= 1`,
  this is the bound, with no dependence on `K`.

**Reduction.**  Let `f` be continuous strictly positive affine on `T(A)`, and
let `eps > 0`.

1. Brown--Perera--Toms Proposition 5.1 (arXiv:math/0609182, read in lane
   `lix-toms-winter-2`), applied with every `A_n = A` and `A` simple, gives
   `0 <= a in A` with `|f(tau) - tau(a)| < eps` on `T(A)`.  Let `K` be an
   integer with `K >= ||a||`.
2. Take `L >= 1/eps` and `b = b_L`.  The bound gives
   `|(1/L) d(b) - tau(a)| <= eps`.
3. Approximate division gives `y` with `|L d(y) - d(b)| < eps L`, that is
   `|d(y) - (1/L) d(b)| < eps`.
4. So `|d(y) - f| < 3 eps` uniformly on `T(A)`.

Since `eps` is arbitrary, rank density holds.
