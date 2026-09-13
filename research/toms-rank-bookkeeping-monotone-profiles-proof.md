---
rg: 2
id: toms-rank-bookkeeping-monotone-profiles-proof
kind: route
title: Ceilings of the leaf average minus two are superadditive under doubling and sandwich the target within 2/r_n
target: toms-rank-bookkeeping-admits-monotone-realizer-profiles
requires: []
---

Imports from arXiv:2606.12188v2, Section 4: `X_(N+1) = X_N x X_N x CP^(j_N)`,
`phi_N(a) = (pi_1^* a tensor gamma_(N,1)) + (pi_2^* a tensor gamma_(N,2))`,
`rank p_N = rank q_N = d_N = 2^(N-1) d`, `p_1 = theta^d`.

**Step 0: the constraints hold for realizers.** Fibre evaluation is a
`*`-homomorphism, so `b <~ c` in `M_infinity(C(X))` gives
`rank b(z) <= rank c(z)` at every `z`. This is (C2). The rank of
`phi_(N,M)(a)` at `z` is `sum_i rank a(z^(i))`, since line-bundle twists do
not change rank. A trace with stage-`N` measure `mu_N` gives
`d_tau(a) = integral rank a(x) / r_N d mu_N(x)` for `a in M_k(A_N)_+`, which is
(C3). Lower semicontinuity of fibre rank is standard, which is (C1).

**Step 1: the target in stage coordinates.** `h in A_1` pushes forward to
`sum_l h(x_l) 1_l`, where the leaf projections `1_l` have fibre rank `d` in
`q_N`. So its normalized fibre trace is `F_N(x)`, and `tau(h) = integral F_N d mu_N`.
For `M > N` the leaves of `X_M` are the leaves of the copies, so
`F_M(z) = (1/M') sum_i F_N(z^(i))` and `r_M F_M(z) = sum_i r_N F_N(z^(i))`.

**Step 2: (C1) and the sandwich.** Put `g = r_n F_n`, a continuous function with
values in `[0, r_n]`. The function `ceil` is lower semicontinuous and
non-decreasing, so `R_n = max(0, ceil(g - 2))` is lower semicontinuous. From
`y <= ceil(y) < y + 1` we get `R_n < max(0, g - 1) <= g` and `R_n >= g - 2`. So
`F_n - 2/r_n <= R_n / r_n <= F_n`, and (C3) follows by integrating, with error
at most `2/r_n -> 0`.

**Step 3: (C2).** Here `M' = 2`. Let `g_1, g_2` be the values of `g` at the two
copies of `z`, so `r_(n+1) F_(n+1)(z) = g_1 + g_2`.
- If both `g_i > 2`: `R_n(z^(1)) + R_n(z^(2)) < (g_1 - 1) + (g_2 - 1) = g_1 + g_2 - 2 <= ceil(g_1 + g_2 - 2)`,
  and the left side is an integer, so it is at most `R_(n+1)(z)`.
- If exactly one `g_i > 2`, the sum is `ceil(g_i - 2) <= ceil(g_1 + g_2 - 2)`.
- If neither, the sum is `0 <= R_(n+1)(z)`.

**Step 4: realization.** `p_n = sum_l theta^d tensor gamma_l` is an orthogonal
sum of `r_n` line subbundles `P_1, ..., P_(r_n)` in a fixed order. Put
`c_j = min(1, max(0, g - 1 - j))` and `a_n = sum_j c_j P_j`. Then `c_j > 0` iff
`j < g - 1`, iff `j <= ceil(g - 2)`, so `rank a_n = R_n`.

**Step 5: all-wall points.** Let `z` have both copies on walls, i.e.
`g_i - 2 = k_i` with `k_i >= 0` integers. Then `R_n(z^(i)) = k_i`, while points
arbitrarily close to `z^(i)` with larger `g` have `R_n = k_i + 1`. And
`R_(n+1)(z) = ceil(g_1 + g_2 - 2) = k_1 + k_2 + 2 >= (k_1 + 1) + (k_2 + 1)`.
So at `z` the next profile already contains the rank beyond both walls.

**What is not claimed.** Nothing here produces `a_n <~ a_(n+1)`. The ramps of
Step 4 use fixed orderings; containment across a wall needs a transport that
moves support from one twisted copy into another, which is exactly the
operator-level question. Square.
