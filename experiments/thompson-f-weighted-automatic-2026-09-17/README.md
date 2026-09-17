# Geodesic combings of Thompson's group F over consecutive generating sets (2026-09-17, sw-104)

Companion computations for `thompson-f-no-geodesic-combing-over-standard-generators`
and the target `zaremsky-2-02-thompson-f-automatic`. All runs were single-threaded
under `nice -n 10 timeout 1200`, in Python 3 with pysat (CaDiCaL 1.5.3).

**Conventions.** The code uses letters `a/A = x0^±1`, `b/B = x1^±1`, `c/C = x2^±1`,
`d/D = x3^±1`. Products are read left to right as "then". Generators satisfy
`x_(j+1) = x_i x_j x_i^-1` for `i < j`. This is the standard presentation with every
`x_i` replaced by its inverse, so the Cayley graphs are isomorphic. Elements are
exact PL maps (`fastF.py`, integer breakpoints scaled by `2^48`).

## Files

| file | purpose |
|---|---|
| `fastF.py` | exact PL arithmetic in F |
| `geocomb_sat.py k R K [group] [core]` | SAT encoding: does `B_R` of `Γ(F, X_k)` carry a geodesic combing with fellow traveller constant `K`? Optionally extracts an unsat core. Calibration groups: `Z2`, `Z3`, `F2` (SAT at small `K`) and `BS12` (UNSAT at `K = 2`). |
| `single_edge.py` | single-edge divergence `D(g, s)` (always 1), and, with `v`, vertex divergence `Dv(h)` = min over geodesics `q` to `h` of max over neighbours `g` of min over geodesics `p` to `g` of `max_t d(q(t), p(t))` |
| `lengthF.py n tokens` | exact length over `X_n` by A* with the heuristic `l_inf` (non-right carets of the reduced tree pair). Validated against BFS distances on 300 random elements each of `B_8(X_1)`, `B_5(X_2)` and `B_4(X_3)`, with 0 mismatches. It is slow when `l_n − l_inf` is large. |
| `seesaw_scan.py k R` | Cleary–Taback seesaw swing w.r.t. `x0` for all elements of `B_R` |
| `geod_mm.py k r words` | meet-in-the-middle lengths and enumeration of all geodesics |
| `pareto.py R`, `mkrws.py` | weighted-metric Pareto profiles over `{x0, x1}`, and KBMAG rewriting-system input (all KBMAG shortlex runs over `X_1`, `X_2` and the weighted orders timed out at 1200 s) |

## Results

**Geodesic-combing SAT on balls** (`sat_F_A.txt`, `sat_F_A_R6.txt`, `sat_F_A2_R4.txt`,
`sat_F_A2_R5.txt`). `K_min` is the least fellow traveller constant of a geodesic
combing of the ball.

| generating set | R | \|B_R\| | K_min |
|---|---|---|---|
| X_1 | 5 | 475 | 4 (K = 2, 3 UNSAT) |
| X_1 | 6 | 1381 | 6 (K = 2, 4, 5 UNSAT) |
| X_2 | 4 | 541 | 2 (K = 1 UNSAT) |
| X_2 | 5 | 2067 | 4 (K = 2, 3 UNSAT) |

An UNSAT answer at `(R, K)` is a finite certificate. By restriction, `(F, X_k)` has no
geodesic combing with constant `K`. The growth of `K_min` with `R` is the finite
shadow of the theorem that no constant works.

The minimal unsat core at `X_1`, `R = 5`, `K = 3` has two edges, `(aabA, A)` and
`(babA, B)`. Both end at `h = aabAA = x_3`, which has exactly two geodesics,
`aabAA` and `babAB`.

**Vertex divergence** (`vertex_A_R7.txt`, `vertex_A2_R6.txt`).
- Over `X_1` on `B_7`, the histogram of `Dv` is `{1: 3809, 4: 94, 6: 54}`. The value 6
  is first reached at length 6 (`AbabbA`) and at `x_4 = aaabAAA`.
- Over `X_2` on `B_6`, it is `{1: 5779, 2: 1784, 4: 182, 6: 8}`. The value 6 is reached
  at `AbaccA` and its symmetric images, and 4 at `aacAA = x_4`.

The obstruction lives at vertices with two geodesic classes that differ in the
first letter, such as `x_m = s_1 ... s_(m−n) x_n S_(m−n) ... S_1`. Neighbours on
either side see only one class.

**Seesaw scan** (`seesaw_scan.py`): over `X_1` on `B_9` there are 402 seesaw
elements of swing 1 and none of swing ≥ 2; the Cleary–Taback swing-`k` words are
longer. Over `X_2` on `B_6` there are none. Balls are too small to see seesaw
behaviour over `X_2`. Proving non-combability through the almost-convexity lemma
avoids needing it.

**Weighted metrics** (`pareto_R10.txt`): every word of length `<= 10` over `{x0, x1}`
that is geodesic for a positive weighting `(p, q)` of `x0, x1` is a standard
geodesic. Positive reweighting does not escape the geodesic obstruction at these
lengths.

## What this does not decide

- Near-geodesic structures with additive excess `c > 0` over `X_n`, `n >= 2`. Over
  `X_1` this is Hauze's theorem.
- Multiplicative quasigeodesic structures over any generating set, which is
  Zaremsky Problem 2.2.
