# Sanov congruence Cayley graphs of SL_2(F_p): numerical spectra

Lane `ex-sl3z-purely-matricial`, 2026-09-13.  Numerical evidence only, no
theorem.

**Why.**  `sl3z-prime-level-sc-forces-congruence-sc-for-sl2z` shows that a
strongly convergent prime-level sequence for `SL_3(Z)` forces
`l^2_0(SL_2(F_p)) -> lambda_(SL_2(Z))` strongly, with no choice of
constituents.  For the Sanov generators `a = [[1,2],[0,1]]`, `b = [[1,0],[2,1]]`
(free, index 12 in `SL_2(Z)`, onto `SL_2(F_p)` for odd `p`), the element
`A = a + a^-1 + b + b^-1` has regular norm `2 sqrt 3 = 3.4641016` (Kesten).  The
claim therefore needs `||l^2_0(SL_2(F_p))(A)|| -> 2 sqrt 3`.

**Method.**  Lanczos iteration (250--300 steps, random start, constants
removed), with the extreme Ritz values located by Sturm bisection.  Ritz values
lie inside the spectrum, so every `norm` below is a **lower bound** for the true
norm.  The programs are `experiments/sl3z-purely-matricial/sanov.c` (modes `G`,
`V`, `P`) and `chisec.c`, run on MSI 2026-09-13.

- `G`: `l^2_0(SL_2(F_p))`, the Cayley graph, covering all sectors.
- `V`: `l^2_0(F_p^2 \ 0)`, which is `Ind_U 1`: all principal series and the
  Steinberg representation.
- `P`: `l^2_0(P^1(F_p))`, the Steinberg representation alone.
- `chisec`: each principal series `Ind_B(chi)` separately.  It is realised on
  `P^1(F_p)` with the multiplier `chi(t_s(z))`, where `s v_z = t_s(z) v_(s.z)`.

## Whole group and the vector sector

| mode | `p` | dimension | `lambda_max` | `lambda_min` | norm (lower bound) |
|---|---|---|---|---|---|
| G | 31 | 29760 | 3.445034 | -3.522112 | 3.522112 |
| G | 61 | 226920 | 3.498734 | -3.531451 | 3.531451 |
| G | 101 | 1030200 | 3.524972 | -3.546935 | 3.546935 |
| G | 151 | 3442800 | 3.530480 | -3.504210 | 3.530480 |
| G | 211 | 9393720 | 3.521668 | -3.521087 | 3.521668 |
| V | 101 | 10200 | 3.524972 | -3.546935 | 3.546935 |
| V | 307 | 94248 | 3.489368 | -3.489900 | 3.489900 |
| V | 1009 | 1018080 | 3.520902 | -3.503458 | 3.520902 |
| V | 3001 | 9006000 | 3.524418 | -3.492886 | 3.524418 |

At `p = 101` the extreme eigenvalues of `G` and `V` agree to six digits, so the
outlier lies in a principal series.

## Steinberg sector alone (`P`, projective line)

| `p` | `lambda_max` | `lambda_min` | norm (lower bound) |
|---|---|---|---|
| 101 | 3.202945 | -3.415226 | 3.415226 |
| 1009 | 3.447633 | -3.458631 | 3.458631 |
| 10007 | 3.456045 | -3.457350 | 3.457350 |
| 100003 | 3.464681 | -3.463253 | 3.464681 |
| 1000003 | 3.464461 | -3.464712 | 3.464712 |
| 10000019 | 3.463965 | -3.463959 | 3.463965 |

The Steinberg sector approaches `2 sqrt 3` from both sides.  Its excess is below
`7 * 10^-4` for `p` up to `10^7`.

## Principal series by character (`chisec`)

| `p` | sectors | largest sector norm (`k`, order of `chi`) | sectors above `2 sqrt 3 + 0.01` |
|---|---|---|---|
| 101 | 100 | 3.546935 (`k = 12, 88`, order 25) | 4 |
| 1009 | 1008 | 3.520902 (`k = 504`, quadratic) | 55 (5.5%) |
| 3001 | 3000 | 3.524418 (`k = 1500`, quadratic) | 111 (3.7%) |
| 10007 | 10006 | 3.488080 (`k = 182, 9824`, order 5003) | 146 (1.5%) |

- At `p = 1009` the next sectors after the quadratic one have orders 36, 504,
  56, 63 and 252, with norms 3.49--3.50.
- At `p = 3001` they have orders 750, 500, 125 and 50, with norms 3.488--3.493.
- At `p = 10007` the quadratic sector is `3.459189` (below `2 sqrt 3`), and the
  top ten sectors all have order 5003.
- No character order stands out consistently: the outliers are spread over many
  sectors.

## Reading

1. Every sector is a 4-regular multiplier graph on `p + 1` vertices.  A single
   sector (Steinberg) is numerically Ramanujan up to `p = 10^7`.  The maximum
   excess over all principal-series sectors is:
   - `0.083` at `p = 101`;
   - `0.057` at `p = 1009`;
   - `0.060` at `p = 3001`;
   - `0.024` at `p = 10007`.
2. The fraction of sectors more than `0.01` above the edge falls from 5.5% to
   1.5%.  Random 4-regular graphs on `n` vertices fluctuate above the edge on
   the Tracy--Widom scale `~ n^(-2/3)`, and a maximum over `~p` sectors decays
   slowly.  The data are consistent with that finite-size picture.
3. This is weak evidence *for* the principal-series part of
   `sl2z-prime-congruence-quotients-converge-strongly`.  No structured outlier
   was found.  The cuspidal sectors were only seen through the whole group
   (`G`, `p <= 211`), where all sectors are mixed.  No sector computation of
   them was done.
