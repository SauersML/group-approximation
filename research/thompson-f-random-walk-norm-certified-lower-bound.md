---
rg: 2
id: thompson-f-random-walk-norm-certified-lower-bound
kind: claim
title: Simple random walk on Thompson's group F has Markov operator norm above 0.8805
distinct_from:
  thompson-f-moment-data-cannot-certify-nonamenability: that shows finite closed-walk counts never prove the norm is below 1; this is the positive direction, a certified lower bound on the norm from the same kind of data.
  thompson-f-random-walks-are-not-liouville: that concerns bounded harmonic functions; this is a quantitative spectral bound for one symmetric walk.
artifacts:
  - experiments/thompson-f/cogrowth_exact.py
  - experiments/thompson-f/out14.json
  - experiments/thompson-f/out15.json
---

**ESTABLISHED (computer-assisted, exact arithmetic).** Let
`P = (x_0 + x_0^{-1} + x_1 + x_1^{-1})/4` act on `l^2(F)`. Then

    ||P|| > 880541/1000000 = 0.880541,

equivalently the norm of `x_0 + x_0^{-1} + x_1 + x_1^{-1}` in `C*_r(F)` exceeds `3.5221`.

**Exact counts.** `c_{2j}` is the number of trivial words of length `2j` in the four letters.
For `j = 0, ..., 15`:

    1, 4, 28, 232, 2092, 19884, 196096, 1988452, 20612364, 217561120,
    2331456068, 25311956784, 277937245744, 3082543843552, 34493827011868,
    389093033592912

**Certificate.** `mu_2` is the spectral measure of `P^2` at `delta_e`, with moments
`M_j = c_{2j}/16^j`.
- The monic orthogonal polynomials `p_0, ..., p_8` are computed exactly from `M_0..M_15`.
- `<p_j, p_j> > 0` for `j < 8`.
- `p_8(theta) < 0` at `theta = 775353449/1000000000`.

By the orthogonality argument (`thompson-f-moment-barrier-proof`, Step 5),
`||P||^2 >= sup supp mu_2 > theta`. Also `(880541/10^6)^2 <= theta`, which gives the bound.

The depth-14 run (`out14.json`, `p_7`) already gave `||P|| > 0.872832`.

**Checks** (in `out14.json` and `out15.json`):
- the maps satisfy both defining relators of `F`, and `x_0`, `x_1` do not commute;
- brute-force enumeration up to length 8 agrees with the dynamic program;
- every `c_{2j}` is at most the `Z^2` count `binom(2j,j)^2`;
- the moments are log-convex;
- the two runs agree on every shared count.

**Trust surface.** One program, not independently reimplemented. It uses exact integer
arithmetic over `2^64`, checks every division for exactness, and canonicalizes minimal
breakpoints.

**Scope.**
- This is a lower bound only. By `thompson-f-moment-data-cannot-certify-nonamenability`, no
  finite data of this kind decides amenability.
- Published numerical estimates (Haagerup–Haagerup–Ramirez-Solano 2015;
  Elder–Rechnitzer–Janse van Rensburg 2015) are uncertified and were not read here. No
  novelty is claimed.

Proof route: `thompson-f-random-walk-norm-lower-bound-proof`.
