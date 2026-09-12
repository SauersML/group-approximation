---
rg: 2
id: thompson-f-random-walk-norm-lower-bound-proof
kind: route
title: Exact closed-walk counts to length 30 and a sign change of the degree-8 orthogonal polynomial
target: thompson-f-random-walk-norm-certified-lower-bound
requires: []
artifacts:
  - experiments/thompson-f/cogrowth_exact.py
  - experiments/thompson-f/out15.json
---

1. **Model.** `x_0` has breakpoints `(1/2, 1/4), (3/4, 1/2)`, and `x_1` has breakpoints
   `(1/2, 1/2), (3/4, 5/8), (7/8, 3/4)`. Elements of `F` are PL homeomorphisms stored by
   minimal breakpoint lists over `2^64`. Composition evaluates exactly and raises an error on
   any inexact division. The script checks that both relators
   `[x_0 x_1^{-1}, x_0^{-1} x_1 x_0]` and `[x_0 x_1^{-1}, x_0^{-2} x_1 x_0^2]` are trivial.

2. **Counts.** `a_j(g)` is the number of words of length `j` evaluating to `g`. It comes from a
   dynamic program over the ball of radius 15; the largest support has 10,133,856 elements.
   - Inversion with letter reversal is a bijection, so `a_j(g^{-1}) = a_j(g)` and
     `c_{2j} = sum_g a_j(g)^2`.
   - Cross-checks: brute force over all `4^L` words for `L <= 8`; the bound
     `c_{2j} <= binom(2j,j)^2`; log-convexity of `M_j = c_{2j}/16^j`.

3. **Certificate.**
   - Build the monic orthogonal polynomials for `M_0, ..., M_15` by the exact three-term
     recurrence, and verify `<p_j, p_j> > 0` for `j < 8`.
   - Exact evaluation gives `p_8(theta) < 0` at `theta = 775353449/1000000000`, so `p_8` has a
     zero above `theta`.
   - The largest zero `x_8` is at most `sup supp mu_2`. Put `q = p_8/(x - x_8)`, so
     `int (x - x_8) q^2 dmu_2 = 0`. A support below `x_8` would put `mu_2` on the 7 zeros of
     `q`, contradicting positive definiteness of the 8×8 Hankel matrix.
   - Hence `||P||^2 > theta >= (880541/10^6)^2`.

4. **Runs.** On MSI msismall, 1 core each:
   - `tf-cogrowth15`: 1167.5 s, peak RSS about 17.5 GB, output `experiments/thompson-f/out15.json`;
   - `tf-cogrowth14`: 262.8 s, output `out14.json`;
   - the two runs agree on `c_0..c_28`.
