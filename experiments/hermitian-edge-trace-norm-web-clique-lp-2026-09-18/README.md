# Per-size Yudin certificates for the clique windows of webs (lane w8-078, 2026-09-18)

Supports `research/hermitian-edge-trace-norm-web-rank-k5-to-k9-per-m-lp.md`.

The large-m clique proof (`research/hermitian-edge-trace-norm-clique-inequality-large-m-proof.md`,
Steps 1-3) gives, for every `m` and every polynomial `F(z) = sum c_pq z^p zbar^q` with `c_pq = c_qp`,
`c_pq >= 0` for `(p,q) != (0,0)`, and `F(z) <= 1/|1-z|` on the closed unit disk minus `z = 1`:

```text
c_m  >=  L_m := 2 (c_00 m^2 - m F(1)) / (m - 1) .
```

That proof uses one `F` (degree 4, tuned for `m = 6`) for all `m`. Here each `m` gets its own `F`,
tuned for that `m`.

| file | m | degree | verify.py boxes | c_00 m^2 - m F(1) | L_m | eps_m = L_m - sqrt3 (m-1) |
|---|---|---|---|---|---|---|
| `F_m6_D10.json` | 6 | 10 | 2331859 | 21.89236 | 8.756945 | 0.09669 |
| `F_m7_D10.json` | 7 | 10 | 1870531 | 31.96515 | 10.655051 | 0.26275 |
| `F_m8_D6.json`  | 8 | 6 | 447371 | 43.93141 | 12.551833 | 0.42748 |
| `F_m9_D6.json`  | 9 | 6 | 403895 | 57.90455 | 14.476138 | 0.61973 |
| `F_m10_D6.json` | 10 | 6 | 374505 | 73.84774 | 16.410609 | 0.82215 |

- **Producing F.** `experiments/hermitian-edge-trace-norm-clique-energy-2026-09-18/cert_lp.py m D eta`,
  unchanged (md5 `e12bd5b6...`), with `eta = 0.002` (`D = 6`) or `0.001` (`D = 10`). It maximises
  `c_00 m^2 - m F(1)` subject to `F <= (1-eta)/|1-z|` on a grid.
- **Checking F.** `experiments/hermitian-edge-trace-norm-clique-energy-2026-09-18/verify.py F.json`,
  unchanged (md5 `8cac707a...`). The logs are `verify_F_*.log`. It rounds the coefficients to
  rationals with denominator `10^7` and proves `F(z) <= 1/|1-z|` on `[0,1] x [0,pi]` in `(r, theta)`
  by outward-rounded interval bisection. Every run prints `verified`.
- **The lists.** `web_clique_lists.py` takes `m:F.json`. It re-derives `c_00` and `F(1)` with the same
  rounding as `verify.py` (they agree with the logs). It computes `L_m` exactly and, for each
  `2k+2 <= n < N`, checks `(n L_m/m)^2 >= 3 (n - floor(n/m))^2` in exact rationals. Here
  `N = floor((m-1) s/eps) + 2`, with `s = 17320509/10^7 > sqrt3` and `eps = L_m - (m-1) s`, so
  `n eps >= sqrt3 (m-1)` for `n >= N`. The output is `web_clique_lists.log`.

Higher degree changes little: `m = 8` with `D = 8, 10` gives `43.98068`, which leaves the list
`{22, 23}` unchanged, and `m = 6` with `D = 12` gives `21.89238`. `k = 7` needs
`c_00 m^2 - m F(1) >= 44.0886` for `n = 22` (`eps_8 >= 6 sqrt3/22`) and `>= 44.2803` for `n = 23`
(`eps_8 >= 7 sqrt3/23`). The LP value is flat in `D` near `43.98`, so both are out of reach of this
route.
