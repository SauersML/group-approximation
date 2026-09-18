# Triangular Harper sum and the qudit Weyl rounding constant (2026-09-18, w3-078)

This directory supports `research/qudit-weyl-rounding-constant-triangular-harper-bound.md`. The
proof does not use it. Every run was single-threaded under `nice -n 10 timeout 1200`, with numpy
and scipy.

`K = Z + Z^* + X + X^* + T + T^*` with `T = e^(i pi/d) XZ = -D(1,1)`, `W = 6`, and `F = W - K`.

## `gauss_trial.py` -> `gauss_trial.log`

For each `d`, this script computes three quantities:
- the exact `F_min`;
- `F(psi)` for the chirped Gaussian `psi(x) = exp(-pi(a - ib)x^2/d)` with `a = sqrt3/2`, `b = 1/2`, on
  `|x| <= (d-1)/2`;
- the ratio `c(K) = 4/F_min - 1`, where `4` is the stabilizer frustration.

| `d` | `F_min` | `F(psi)` | `2 sqrt3 pi/d` | `c(K)` | `2d/(sqrt3 pi) - 1` | `d/pi` |
|---|---|---|---|---|---|---|
| 5 | 1.821683 | 1.822042 | 2.176559 | 1.1958 | 0.8378 | 1.5915 |
| 7 | 1.369390 | 1.369475 | 1.554685 | 1.9210 | 1.5729 | 2.2282 |
| 11 | 0.912075 | 0.912082 | 0.989345 | 3.3856 | 3.0431 | 3.5014 |
| 13 | 0.781359 | 0.781362 | 0.837138 | 4.1193 | 3.7782 | 4.1380 |
| 31 | 0.340985 | 0.340985 | 0.351058 | 10.7307 | 10.3941 | 9.8676 |
| 61 | 0.175780 | 0.175780 | 0.178406 | 21.7557 | 21.4207 | 19.4169 |
| 101 | 0.106789 | 0.106789 | 0.107750 | 36.4571 | 36.1228 | 32.1493 |
| 211 | 0.051356 | 0.051356 | 0.051577 | 76.8874 | 76.5536 | 67.1634 |
| 401 | 0.027078 | 0.027078 | 0.027139 | 146.7222 | 146.3886 | 127.6423 |

Observations:
- `F(psi) <= 2 sqrt3 pi/d` in every row, and the Gaussian is almost exactly the ground state.
- `c(K) - (2d/(sqrt3 pi) - 1)` tends to about `1/3`.
- The square Harper values from `qudit-weyl-rounding-sharp-constant` are `0.935, 1.510, 2.765, 3.399,
  9.12, 18.67, 31.40, 66.41` for `d = 5, ..., 211`.
- The triangle is larger for every `d >= 5`, and it exceeds `d/pi` from `d = 31` on.

## `tri_quick.py` -> `tri_quick.log`

This script uses the best stabilizer value over all `d(d+1)` one-qudit stabilizer states,
computed directly (it is `2`). It compares the two signs on `D(1, +-1)`:
- `-D(1,1)` gives the table above;
- `+D(1,1)` is frustrated and gives `c = 0.2297, 0.2056, 0.2027, 0.2087, 0.2646, 0.2961, 0.3103` for `d = 5, 7, 11, 13, 31, 61, 101`.

The directions `D(1,1)` and `D(1,-1)` give identical values.

## `exact_direction_search.py` -> `exact_direction_search.log`

This is an exact one-qudit check of whether more directions help. The sum is
`K = sum_j w_j (u_j + u_j^*)` over the six directions `(0,1), (1,0), (1,1), (1,-1), (1,2), (2,1)`,
with BCH phases `e^(i pi ab/d)`. Weights are random: exponential, each switched off with
probability 0.3. The best stabilizer value is exact.
- `d = 13`, 400 weightings: best `c = 4.1193`, the triangle.
- `d = 31`, 300 weightings: best `c = 10.7307`, the triangle.

## `semiclassical_search.py` -> `semiclassical_search.log`

In the small-angle regime `c ~ (d/2pi) rho` with `rho = 4(W - m_iso)/||D Omega D||_1`. Here
`Omega` is the integer symplectic Gram matrix of `k` directions, `D = diag(sqrt w)`, and `m_iso` is
the maximum weight of a commuting set. The script enumerates all `Omega` with entries in
`{-1, 0, 1}`, which includes multi-qudit configurations, and optimizes the weights by Nelder–Mead.
- `k = 2`: `rho = 2`, the square Harper sum.
- `k = 3`: `rho = 2.30940 = 4/sqrt3`, the triangle.
- `k = 4`: `rho = 2.30940`, a triangle with a split vertex.
- `k = 5`: the exhaustive run (59049 matrices) did not finish within the 1200 s limit (`exit=124` in the log).

The one-qudit bound `rho <= 4/sqrt3` follows heuristically from Motzkin–Straus on the
`K_4`-free Farey graph.
