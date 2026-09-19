---
rg: 2
id: hermitian-edge-trace-norm-web-rank-k5-to-k9-per-m-lp
kind: route
title: Clique windows K_{k+1} with a Yudin certificate tuned to each clique size m = 6..10, then an exact finite check
target: hermitian-edge-trace-norm-web-rank-k5-to-k9
requires:
  - hermitian-edge-trace-norm-clique-inequality-large-m
artifacts:
  - research/hermitian-edge-trace-norm-clique-inequality-large-m-proof.md
  - research/hermitian-edge-trace-norm-web-rank-large-k-clique-windows.md
  - experiments/hermitian-edge-trace-norm-clique-energy-2026-09-18/verify.py
  - experiments/hermitian-edge-trace-norm-clique-energy-2026-09-18/cert_lp.py
  - experiments/hermitian-edge-trace-norm-web-clique-lp-2026-09-18/README.md
  - experiments/hermitian-edge-trace-norm-web-clique-lp-2026-09-18/F_m6_D10.json
  - experiments/hermitian-edge-trace-norm-web-clique-lp-2026-09-18/F_m7_D10.json
  - experiments/hermitian-edge-trace-norm-web-clique-lp-2026-09-18/F_m8_D6.json
  - experiments/hermitian-edge-trace-norm-web-clique-lp-2026-09-18/F_m9_D6.json
  - experiments/hermitian-edge-trace-norm-web-clique-lp-2026-09-18/F_m10_D6.json
  - experiments/hermitian-edge-trace-norm-web-clique-lp-2026-09-18/verify_F_m6_D10.log
  - experiments/hermitian-edge-trace-norm-web-clique-lp-2026-09-18/verify_F_m7_D10.log
  - experiments/hermitian-edge-trace-norm-web-clique-lp-2026-09-18/verify_F_m8_D6.log
  - experiments/hermitian-edge-trace-norm-web-clique-lp-2026-09-18/verify_F_m9_D6.log
  - experiments/hermitian-edge-trace-norm-web-clique-lp-2026-09-18/verify_F_m10_D6.log
  - experiments/hermitian-edge-trace-norm-web-clique-lp-2026-09-18/web_clique_lists.py
  - experiments/hermitian-edge-trace-norm-web-clique-lp-2026-09-18/web_clique_lists.log
---

An ordinary proof plus five computer-verified polynomial inequalities. It is unreviewed and not
Lean-verified. Lane w8-078, 2026-09-18. Files are in
`experiments/hermitian-edge-trace-norm-web-clique-lp-2026-09-18/`.

Let `m = k + 1` with `6 <= m <= 10`, `n >= 2m`, and `n = q m + r` with `0 <= r <= m - 1`. Let `c_m` be
the minimum of `||C||_1` over admissible `C` on `K_m`.

## Step 1. Windows

This is Step 1 of `hermitian-edge-trace-norm-web-rank-large-k-clique-windows`. The `n` sets
`{t, ..., t+k}` (mod `n`) are cliques of `C_n^k` and cover every vertex `m` times. The covering lemma
(Lemma 1 of `hermitian-edge-trace-norm-odd-antihole-facets-by-size`) gives
`||C||_1 >= (n/m) c_m`. So `(R_{n,k})` holds whenever `(n L/m)^2 >= 3 (n - q)^2` for some
`0 < L <= c_m`.

## Step 2. A lower bound on `c_m` for each `m`

Steps 1-3 of `hermitian-edge-trace-norm-clique-inequality-large-m-proof` hold for every `m` and every
`F` satisfying Lemma 3 there: `F = sum c_pq z^p zbar^q` with `c_pq = c_qp`, `c_pq >= 0` for
`(p,q) != (0,0)`, and `F(z) <= 1/|1-z|` for `|z| <= 1`, `z != 1`. They give
`||C||_1 >= 2 (c_00 m^2 - m F(1))/(m-1)` for every Hermitian `m x m` `C` with zero diagonal and
`|C_ij| >= 1` off the diagonal. That class contains every admissible `C` on `K_m`. So

```text
c_m  >=  L_m := 2 (c_00 m^2 - m F(1)) / (m - 1) .
```

The large-m proof takes one `F` (degree 4). Here `F_m{m}_D{D}.json` is the optimum of that proof's LP
(`cert_lp.py m D eta`) for the given `m`. Its coefficients, rounded to rationals with denominator
`10^7` (negative non-constant coefficients set to `0`; there are none), are printed at the top of each
`verify_F_*.log`. Each log ends Lemma 4 of the large-m proof for that `F` with `verified`, using the
same `verify.py` and the same outward-rounded interval bisection:

| m | degree | boxes | c_00 m^2 - m F(1) | L_m |
|---|---|---|---|---|
| 6 | 10 | 2331859 | 21.89236 | 8.756945 |
| 7 | 10 | 1870531 | 31.96515 | 10.655051 |
| 8 | 6 | 447371 | 43.93141 | 12.551833 |
| 9 | 6 | 403895 | 57.90455 | 14.476138 |
| 10 | 6 | 374505 | 73.84774 | 16.410609 |

## Step 3. Arithmetic

`web_clique_lists.py` recomputes `c_00` and `F(1)` from each JSON with the same rounding, so they
match the logs, and forms `L_m` as an exact rational. Let `s = 17320509/10^7 > sqrt3` and
`eps = L_m - (m-1) s > 0`, so `eps <= L_m - sqrt3 (m-1)`. Since `n - q = ((m-1) n + r)/m`, the
inequality of Step 1 with `L = L_m` is equivalent to `n (L_m - sqrt3 (m-1)) >= sqrt3 r`. It holds when
`n eps >= s (m-1)`, that is for every `n >= N := floor((m-1) s/eps) + 2`. For `2m <= n < N` the script
checks `(n L_m/m)^2 >= 3 (n-q)^2` exactly. `web_clique_lists.log` lists the failures:

```text
k=5  N=91  fails at 13-17, 20-23, 26-29, 32-35, 39-41, 45-47, 51-53, 58, 59, 64, 65, 70, 71, 77, 83, 89
k=6  N=41  fails at 17, 18, 19, 20, 25, 26, 27, 34
k=7  N=30  fails at 22, 23
k=8  N=24  no failure
k=9  N=20  no failure
```

Every other `n >= 2m` satisfies `(R_{n,k})`. ∎
