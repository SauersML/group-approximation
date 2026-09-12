---
rg: 2
id: thompson-f-random-walk-norm-lower-bound-proof
kind: route
title: Exact closed-walk counts to length 28 and a sign change of the degree-7 orthogonal polynomial
target: thompson-f-random-walk-norm-certified-lower-bound
requires: []
artifacts:
  - experiments/thompson-f/cogrowth_exact.py
  - experiments/thompson-f/out14.json
---

1. **Model.** `x_0` has breakpoints `(1/2, 1/4), (3/4, 1/2)`. `x_1` has breakpoints
   `(1/2, 1/2), (3/4, 5/8), (7/8, 3/4)`. Group elements are PL homeomorphisms, stored by their
   minimal breakpoint lists with coordinates over `2^64`. Composition evaluates exactly and
   raises an error on any inexact division. The script checks that both relators
   `[x_0 x_1^{-1}, x_0^{-1} x_1 x_0]` and `[x_0 x_1^{-1}, x_0^{-2} x_1 x_0^2]` evaluate to the
   identity, so the generated group is `F`.

2. **Counts.** `a_j(g)` counts words of length `j` evaluating to `g`. It is computed by a
   dynamic program over the ball of radius 14; the largest support has 3,722,149 elements.
   Inversion with letter reversal is a bijection, so `a_j(g^{-1}) = a_j(g)`, and hence
   `c_{2j} = sum_g a_j(g)^2`. Cross-checks:
   - brute force over all `4^L` words for `L <= 8`;
   - the bound `c_{2j} <= binom(2j,j)^2` from the abelianization `Z^2`;
   - log-convexity of `M_j = c_{2j}/16^j`.

3. **Certificate.** Monic orthogonal polynomials for the moment functional
   `M_0, ..., M_13` are built by the exact three-term recurrence, and
   `<p_j, p_j> > 0` is verified for `j < 7`. Exact evaluation gives `p_7(theta) < 0` at
   `theta = 380918149/500000000`, so `p_7` has a zero above `theta`. The largest zero `x_7` is
   at most `sup supp mu_2`:
   - put `q = p_7/(x - x_7)`; then `int (x - x_7) q^2 dmu_2 = 0`;
   - if `supp mu_2` lay below `x_7`, `mu_2` would sit on the 6 zeros of `q`, contradicting
     positive definiteness of the 7×7 Hankel matrix.

   So `||P||^2 >= sup supp mu_2 > theta`, and `13638/15625` squared is below `theta`.

4. **Run.** MSI job `tf-cogrowth14` on msismall, 262.8 seconds, 1 core; output
   `experiments/thompson-f/out14.json`.
