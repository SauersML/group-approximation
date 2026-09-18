---
rg: 2
id: parallel-repetition-threshold-rank-proof
kind: route
title: Symmetrize the bipartite walk, identify the repeated normalized biadjacency as a Kronecker power, and count singular-value products
target: parallel-repetition-collapses-threshold-rank-to-spectral-gap
requires: []
artifacts:
  - experiments/ugc-deficit-ratio-2026-09-17/check_repetition_spectrum.py
---

Notation is as in the target claim. Item 3 reads the hypotheses of
`spectral-gap-no-outputs-cannot-prove-ugc` but uses none of its conclusions.

**Symmetrization.** Let `D` be diagonal with `D(x, x) = deg(x)`. Then
`D^(1/2) A D^(-1/2)` has entries `w(x, y)/sqrt(deg(x) deg(y))`, so it is the
symmetric block matrix `S = [[0, M], [M^T, 0]]`, and `A` is similar to `S`. If
`M = U Sigma V^T` is a singular value decomposition, then `(u_i, +-v_i)/sqrt 2`
are eigenvectors of `S` with eigenvalues `+-s_i`, and the remaining eigenvalues
are `0`. For `0 < gamma < 1`, `1 - gamma > 0`, so `r_gamma(G)` is the number of
indices `i` with `s_i > 1 - gamma`.

**Top singular value.** `M` sends the vector `(sqrt(deg(v)))_v` to
`(sum_v w(u, v)/sqrt(deg(u)))_u = (sqrt(deg(u)))_u`. So `1` is a singular value.
By Cauchy--Schwarz, `|<f, M g>| <= ||f|| ||g||`, since
`sum w(u,v) |f_u g_v|/sqrt(deg u deg v) <= (sum w f_u^2/deg u)^(1/2) (sum w g_v^2/deg v)^(1/2)`.
So `s_1 = 1`.

**Repetition is a Kronecker power.** In `G^n` the total weight between
`u = (u_t)` and `v = (v_t)` sums `prod_t w_(e_t)` over tuples of edges with
`e_t` between `u_t` and `v_t`. That sum factorizes as `prod_t w(u_t, v_t)`.
Summing over `v` gives `deg(u) = prod_t deg(u_t)`, and likewise on the right.
Hence `M_(G^n) = M^(x n)`. From `M^(x n) = U^(x n) Sigma^(x n) (V^(x n))^T`, its
singular values are the products `s_(i_1) ... s_(i_n)` over index tuples. With
the symmetrization, this is **item 1**.

**Item 2.** Suppose `m = 0`. Then `s_2 <= 1 - gamma < 1`. A tuple with some
`i_t >= 2` has product at most `s_(i_t) <= 1 - gamma`, since all factors are
at most 1. So only the all-ones tuple counts, and `r_gamma(G^n) = 1`. The
largest product other than `s_1^n` is `s_2`, attained with one index `2`. So the
second singular value of `G^n` is `s_2(G)`. Now suppose `m >= 1`. The all-ones
tuple and the `n m` tuples with `i_t in {2, ..., m+1}` in one position `t` and
`1` elsewhere are distinct. Each has product `1` or `s_(i_t) > 1 - gamma`. So
`r_gamma(G^n) >= n m + 1`. `square`

**Item 3.** Let `1 <= r <= n`. If `s_2 <= 1 - gamma`, then `m = 0` and
`r_gamma(G^n) = 1 <= r`. If `s_2 > 1 - gamma`, then `m >= 1` and
`r_gamma(G^n) >= n + 1 > r`. This proves the first sentence.

The admissibility condition of item 2 of the kill is
`1536 eps0/gamma + 28 eps0 + 18 r^(2/3) (2 eps0)^(1/3) < 1 - delta`. All terms
are nonnegative, so `18 r^(2/3) (2 eps0)^(1/3) < 1 - delta`. That gives
`r^(2/3) < (1 - delta)/(18 (2 eps0)^(1/3))` and `r < r*`. It also gives
`gamma > 1536 eps0/(1 - delta - 28 eps0)`. The condition is monotone
increasing in `r`, so if `(r, gamma)` is admissible, then so is `(1, gamma)`.

* (only if) An admissible `(r, gamma)` has `r < r* <= n`. So
  `r_gamma(G^n) <= r` gives `s_2 <= 1 - gamma` by the first sentence.
* (if) Suppose `gamma` is admissible and `s_2 <= 1 - gamma`. Then `(1, gamma)` is
  admissible and `r_gamma(G^n) = 1`.

`square`

**Check.** `experiments/ugc-deficit-ratio-2026-09-17/check_repetition_spectrum.py`
builds random small bipartite games and their 2- and 3-fold repetitions
literally, edge tuple by edge tuple. It compares the walk eigenvalues with the
singular-value products and tests the dichotomy of item 2 at random `gamma`.
It is confirmation, not part of the proof.
