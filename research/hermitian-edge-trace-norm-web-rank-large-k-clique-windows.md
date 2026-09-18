---
rg: 2
id: hermitian-edge-trace-norm-web-rank-large-k-clique-windows
kind: route
title: Cover C_n^k by its n cliques of k+1 consecutive vertices and use the large-m clique bound 2(c_00 m^2 - m F(1))/(m-1) with an exact tail check
target: hermitian-edge-trace-norm-web-rank-large-k
requires:
  - hermitian-edge-trace-norm-clique-inequality-large-m
artifacts:
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/web_tail_check.py
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/web_tail_check.log
  - research/hermitian-edge-trace-norm-clique-inequality-large-m-proof.md
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/graphbb.py
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/k4_c9bar.log
---

Notation is as in the target. `m = k + 1`, `n >= 2k + 2 = 2m`, and `n = q m + r` with
`0 <= r <= m - 1`, so `q = floor(n/m) = alpha(C_n^k)` and `q >= 2`. Let `c_m` be the minimum of
`||C||_1` over admissible `C` on `K_m`.

## Step 1. Covering lemma

**Lemma 1.** If `U_1, ..., U_N` are vertex sets that cover every vertex exactly `lambda` times, then

```text
|| C ||_1  >=  (1/lambda) sum_t || C_{U_t} ||_1 .
```

*Proof.* Let `P_t : C^n -> C^{U_t}` be the coordinate restriction, so `C_{U_t} = P_t C P_t^*` and
`sum_t P_t^* P_t = lambda I`. Choose `Z_t` with `||Z_t||_op <= 1` and
`Re tr(Z_t C_{U_t}) = ||C_{U_t}||_1`. Let `A x = (P_t x)_t`, a map from `C^n` into the direct sum
of the `C^{U_t}`. Then `A^* A = lambda I`, so `||A||^2 = lambda`. Put

```text
Z  =  (1/lambda) sum_t P_t^* Z_t P_t  =  (1/lambda) A^* (diag_t Z_t) A .
```

Then `||Z||_op <= (1/lambda) ||A||^2 max_t ||Z_t||_op <= 1`. Also
`tr(P_t^* Z_t P_t C) = tr(Z_t C_{U_t})`. Hence
`||C||_1 >= Re tr(Z C) = (1/lambda) sum_t ||C_{U_t}||_1`. ∎

(This is the covering lemma used in `hermitian-edge-trace-norm-odd-antihole-facets-by-size` and
`hermitian-edge-trace-norm-web-rank-k2-windows`.)

## Step 2. Clique windows

For `t in Z_n`, let `U_t = {t, t+1, ..., t+k}`. Any two of its vertices have cyclic distance at most
`k`, so `U_t` is a clique `K_m` of `C_n^k`, and the restriction of an admissible `C` to `U_t` is
admissible on `K_m`. Since `n >= m`, the `n` windows are distinct and each vertex lies in exactly
`m` of them. By Lemma 1,

```text
|| C ||_1  >=  (n/m) c_m .
```

This is at least `sqrt3 (n - q)` iff `n c_m >= sqrt3 (m n - m q) = sqrt3 (n (m-1) + r)`, that is,

```text
(W)     n eps_m  >=  sqrt3 r ,        eps_m := c_m - sqrt3 (m-1) .
```

## Step 3. The clique bounds

- `m >= 6` (and in fact every `m >= 2`). Steps 1-4 of
  `hermitian-edge-trace-norm-clique-inequality-large-m-proof` hold for every `m` and give
  `c_m >= L(m) := 2 (c_00 m^2 - m F(1))/(m-1)`, with `c_00 = 4512199/5000000` and
  `F(1) = 8906037/5000000`. This is stated there as the first line of Step 5. The only
  computer-verified input is its Lemma 4, `F(z) <= 1/|1-z|` on the unit disc.
- `m = 4`. `graphbb.py K4 5.3887 2.7 3` certifies `c_4 >= 5.3887` (`k4_c9bar.log`, 1984 boxes; this
  is the certificate for `n = 9` in `hermitian-edge-trace-norm-odd-antihole-facets-by-size`).
- `m = 5`. Only `c_5 >= 4 sqrt3` is certified, so `eps_5 >= 0` and `(W)` holds only when `r = 0`.
  This is why `k = 4` is excluded.

## Step 4. k >= 10 for every n

Since `q >= 2`, we have `n >= 2m + r`, so `(W)` follows from `eps_m >= sqrt3 r/(2m + r)`. The
right-hand side increases with `r`, so it suffices that

```text
eps_m (3m - 1)  >=  sqrt3 (m - 1) .
```

With `c_m >= L(m)`, multiply by `m - 1 > 0`. It suffices that

```text
p(m)  :=  (3m-1) ( 2 c_00 m^2 - 2 F(1) m - sqrt3 (m-1)^2 )  -  sqrt3 (m-1)^2  >  0 .
```

`web_tail_check.py` expands `p(11 + x)` exactly, with coefficients of the form `a_i + b_i sqrt3`
where `a_i, b_i` are rational. It bounds each coefficient below using
`17320508/10^7 < sqrt3 < 17320509/10^7`, taking the endpoint according to the sign of `b_i`. The
lower bounds are

```text
x^0: 18.7558   x^1: 31.4807   x^2: 5.1102   x^3: 0.2185
```

All are positive, so `p(m) > 0` for every real `m >= 11`, which is every `k >= 10`. This proves (a).
The script also checks that the sufficient condition fails for `m = 6..10`, so the small `k` need
Step 5.

## Step 5. The finite lists for k = 3 and 5 <= k <= 9

For fixed `m` with a certified rational `c_m`, `(W)` is equivalent to
`(n c_m)^2 >= 3 (n (m-1) + r)^2`, which the script tests exactly. For `m = 4` it uses `5.3887`. For
`m >= 6` it uses `L(m)`. Let `eps_lo = c_m - (17320509/10^7)(m-1)`, which is a lower bound for
`eps_m`. Since `r <= m - 1`, `(W)` holds for every `n >= N_0 := floor(sqrt3 (m-1)/eps_lo) + 1`,
with the upper rational bound for `sqrt3`. The script tests every `n` in `[2k+2, N_0]` exactly.
The `n` that fail are the exceptions listed in the target (`web_tail_check.log`):

| k | eps_m >= | N_0 | exceptions |
|---|---|---|---|
| 3 | 0.19255 | 27 | 10, 11, 14, 15, 19, 23 |
| 5 | 0.05998 | 145 | 62 values in 13..143 |
| 6 | 0.19139 | 55 | 16-20, 24-27, 32-34, 40, 41, 48 |
| 7 | 0.30607 | 40 | 20-23, 30, 31, 39 |
| 8 | 0.41028 | 34 | 24, 25, 26 |
| 9 | 0.50752 | 31 | 29 |

The `n` with `r = 0` never fail. This proves (b)-(g). ∎

**Verification tier.** The argument is an ordinary proof. It uses two certified inputs: Lemma 4 of
the large-m proof (interval arithmetic) and, for `k = 3` only, the `K_4` branch-and-bound
certificate. The arithmetic of Steps 4-5 is exact rational arithmetic (`web_tail_check.py`,
`python3 web_tail_check.py`, under a second).
