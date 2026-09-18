---
rg: 2
id: mass-only-spectral-relaxation-order-c-proof
kind: route
title: Check the mass bounds for nu_c by independence of e_1..e_m, then average the dominance ratio over the dual vectors a_1..a_m and count how many of them a codimension-c subgroup can contain
target: mass-only-spectral-relaxation-of-subgroup-dominance-is-order-c
requires: []
---

Notation as in the target: `m = 2^c - 1`, `k >= m`, and
`nu_c = 2^-c (delta_0 + sum_(i<=m) delta_(e_i))`, total mass `2^-c (1 + m) = 1`.

## Step 1: feasibility

`nu_c(0) = 2^-c`. Let `W` be a character subspace and
`J = {i <= m : e_i in W}`. The `e_i` are linearly independent, so
`|J| <= dim W`. Hence
`nu_c(W) = 2^-c (1 + |J|) <= 2^-c 2^|J| <= 2^(dim W - c)`, using `1 + j <= 2^j` for
integers `j >= 0`. Also `nu_c(W) <= 1`.

## Step 2: the displacement profile

Let `a_1, ..., a_k` be the standard basis of the group side, so `e_i.a_j = [i = j]`.
For `a` in `F_2^k`, `d_(nu_c)(a) = 2 * 2^-c * #{i <= m : a_i-coordinate of a is 1}`.
In particular `d(a_j) = 2^(1-c)` for `j <= m`. Also `d(a) = 0` exactly for `a` in
`Z = span(a_(m+1), ..., a_k)`.

## Step 3: counting

Let `p` be any law on subgroups of index `2^c` with `max_a Pr_p[a not in H]/d(a) = K`
finite. By the convention, every `H` in the support of `p` contains `Z`. For such
`H`, `H/Z` has codimension `c` in `F_2^k / Z`, which is isomorphic to `F_2^m` with
basis the images of `a_1, ..., a_m`. At most `dim(H/Z) = m - c` independent vectors
lie in `H/Z`. So at least `c` of `a_1, ..., a_m` lie outside `H`. Averaging over
`j <= m`,

```text
K >= (1/m) sum_(j<=m) Pr_p[a_j not in H] / 2^(1-c)
  =  E_p[ #{j <= m : a_j not in H} ] / (m 2^(1-c))
  >= c / (m 2^(1-c))  =  c 2^(c-1) / (2^c - 1)  =  L_c .
```

Since `2^(c-1)/(2^c - 1) > 1/2`, `L_c > c/2`. For `w` uniform on `a_1..a_m` this is the
dual statement `Phi_w(nu_c) = 2^(1-c)` and `min_H w(F_2^k \ H) >= c/m`.

## Step 4: the gap to the stopping-time bound

`E_c/2 - L_c = (1/2)(c + sum_(i<=c) 1/(2^i - 1)) - (c/2)(1 + 1/(2^c - 1))
= (1/2)(sum_(i<=c) 1/(2^i - 1) - c/(2^c - 1))`. This is `<= (1/2) sum_(i>=1) 1/(2^i - 1) < 0.81`.

## Step 5: the violated Harper bound

For `B = span(a_1, ..., a_m)` (the whole space when `k = m`),
`B^perp` contains `0` and none of `e_1..e_m`, so `nu_c(B^perp) = 2^-c` and (H) would require
`2 sum_(j<=m) nu_c{chi.a_j = 1} >= c`. The left side is `2 m 2^-c = 2(1 - 2^-c) < 2`,
which is `< c` for `c >= 2`. (For `c = 2`: `3/2 < 2`.)  QED
