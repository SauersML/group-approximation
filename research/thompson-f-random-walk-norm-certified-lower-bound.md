---
rg: 2
id: thompson-f-random-walk-norm-certified-lower-bound
kind: claim
title: Simple random walk on Thompson's group F has Markov operator norm above 0.8728
distinct_from:
  thompson-f-moment-data-cannot-certify-nonamenability: that shows finite closed-walk counts never prove the norm is below 1; this is the positive direction, a certified lower bound on the norm from the same kind of data.
  thompson-f-random-walks-are-not-liouville: that concerns bounded harmonic functions; this is a quantitative spectral bound for one symmetric walk.
artifacts:
  - experiments/thompson-f/cogrowth_exact.py
  - experiments/thompson-f/out14.json
---

**ESTABLISHED (computer-assisted, exact arithmetic).** For
`P = (x_0 + x_0^{-1} + x_1 + x_1^{-1})/4` on `l^2(F)`:

    ||P|| > 13638/15625 = 0.872832,

equivalently `||x_0 + x_0^{-1} + x_1 + x_1^{-1}||` in `C*_r(F)` exceeds `3.4913`.

**Exact counts.** `c_{2j}` is the number of trivial words of length `2j` in the four letters.
For `j = 0, ..., 14`:

    1, 4, 28, 232, 2092, 19884, 196096, 1988452, 20612364, 217561120,
    2331456068, 25311956784, 277937245744, 3082543843552, 34493827011868

**Certificate.** Let `mu_2` be the spectral measure of `P^2` at `delta_e`, with moments
`M_j = c_{2j}/16^j`.
- The monic orthogonal polynomials `p_0, ..., p_7` are computed exactly from `M_0..M_13`.
- `<p_j, p_j> > 0` holds for `j < 7`.
- `p_7(theta) < 0` at `theta = 380918149/500000000`.

By the orthogonality argument in `thompson-f-moment-barrier-proof`, Step 5, this gives
`||P||^2 >= sup supp mu_2 > theta`. The bound follows since `(13638/15625)^2 <= theta`.

**Checks** (in `experiments/thompson-f/out14.json`):
- the maps satisfy both defining relators of `F`, and `x_0`, `x_1` do not commute;
- brute-force enumeration of all words up to length 8 agrees with the dynamic program;
- every `c_{2j}` is at most the `Z^2` count `binom(2j,j)^2`;
- the moments are log-convex, as they must be for a spectral measure.

**Trust surface.** The count rests on the correctness of one program. It uses exact
integer arithmetic over `2^64`, checks every division for exactness, and canonicalizes minimal
breakpoints. It has not been independently reimplemented.

**Scope.**
- This is a lower bound only. By `thompson-f-moment-data-cannot-certify-nonamenability`, no
  data of this kind decides amenability.
- Published numerical estimates (Haagerup–Haagerup–Ramirez-Solano 2015;
  Elder–Rechnitzer–Janse van Rensburg 2015) are uncertified and are not reproduced here. No
  novelty is claimed.

Proof route: `thompson-f-random-walk-norm-lower-bound-proof`.
