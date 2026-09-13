# Numerics: nonlinear elements, every degenerate principal series, and edge statistics for congruence Schreier graphs of a thin free pair

Lane `ex2-cubic-ihara-bass`, 2026-09-13.  This is evidence, not proof.  It extends
`research/artifacts/cubic-division-congruence-numerics-2026-09-13.md`.  The algebra is the same,
`D = (Q(2cos 2pi/7)/Q, sigma, 2)`, and so are the pairs: the certified free pair `A = a^19, B = b^19`
("m = 19") and the uncertified pair `A = a, B = b` ("m = 1").  It tests necessary conditions for
`cubic-division-free-pair-p2-schreier-asymptotically-ramanujan` and
`cubic-division-congruence-representations-converge-strongly`.

## Code and method

- **Build.**  `cat experiments/cubic-division-sc/sc_p2.c experiments/cubic-ihara-bass/ib_main.c > ib.c`,
  then `gcc -O2 -std=gnu99 -o ib ib.c -lm` (MSI, gcc 8.5).
- **Run.**  `ib run p <9 coeffs of u> m space ctl elem k seed`.  The job scripts `job1.sh`, `job2.sh` and
  `job3.sh` list every command; raw output is in `res1.txt`, `res2.txt` and `res3.txt`.
- **Operator.**  `f -> sum_w f(w x)` over a symmetric word set.  Lanczos runs without
  reorthogonalisation, with constants projected out each step, and the extreme Ritz values are found by
  Sturm bisection.  Ritz values lie inside the spectrum, so a **positive excess is a genuine eigenvalue**
  above the reference.  A negative excess of order `1e-4` at `N ~ 1e6` is Lanczos shortfall.
- **Sanity check.**  At `p = 307`, element 0, `k = 600`, the code reproduces the predecessor's excess
  `-0.000714` to six digits.
- **Spaces.**  Space 0 is `P^2(F_p)` (`N = p^2+p+1`).  Space 1 is `F_p^3 minus 0` (`N = p^3-1`), which is
  `l^2(P^2) + sum_(chi != 1) Ind_P^G(chi o alpha)`: every degenerate principal series at once.  The
  predecessor tested only `chi = 1` and the Legendre character.
- **Controls.**  ctl 2: `A, B` Haar-random in `SL_3(F_p)`.  ctl 3: `A, B` uniformly random permutations of
  the same `N` points (strongly convergent by Bordenave--Collins).

## Elements and exact regular spectra

| elem | `z` | regular spectrum | reason |
|---|---|---|---|
| 0 | `A + A^-1 + B + B^-1` | `[-2 sqrt 3, 2 sqrt 3]` | Kesten |
| 1 | `AB + (AB)^-1 + A^-1B + (A^-1B)^-1` | `[-2 sqrt 3, 2 sqrt 3]` | `AB, A^-1B` is a free basis |
| 2 | `A^2 + A^-2 + B^2 + B^-2 + AB + (AB)^-1` | `[-2 sqrt 5, 2 sqrt 5]` | `A^2, B^2, AB` is a free basis |
| 3 | `A + A^-1 + B + B^-1 + AB + (AB)^-1` | `[-3, 5]` | tree of triangles, below |
| 4 | `A + A^-1 + B + B^-1 + [A,B] + [A,B]^-1` | unknown | random-permutation extremes `4.66408`, `-4.20976` |

- **Free bases (Stallings folding).**
  - For `AB, A^-1B` the folded graph has 2 vertices and 3 edges and one vertex lacks an outgoing `B`.
    So it is rank 2 and of infinite index.
  - For `A^2, B^2, AB` it has 2 vertices and 4 edges, with every label once in each direction.
    So it is rank 3: the index-2 even-length subgroup.
- **Element 3.**
  - Let `T_g = {g, ga, gab}`, `M` the vertex--triangle incidence matrix, and `I` the bipartite incidence
    graph.  `F_2` acts freely on `I` with quotient 2 nodes and 3 edges `e_0, e_1, e_2`.
  - The loops `e_0 e_1^-1` and `e_0 e_2^-1` have monodromy `a` and `ab`, a free basis.  So the monodromy
    `pi_1(quotient) = F_2 -> F_2` is an isomorphism and `I` is the 3-regular tree.
  - Each edge `{g, gs}`, `s in {a, b, ab}^(+-1)`, lies in exactly one `T_k`, so `M M^T = 3 + z`.
  - The tree's adjacency has spectrum `[-2 sqrt 2, 2 sqrt 2]`, so `spec(M M^T) = [0, 8]` and
    `spec(z) = [-3, 5]`.
  - The same identity holds in every Schreier graph, with triangles `{x, Bx, ABx}`.  So `z >= -3` exactly
    there, and "no outlier above 5" is the Ramanujan property of a 3-regular bipartite incidence graph.

## Job 1: nonlinear elements on `P^2(F_p)`

Every split prime `300 < p < 1000` (36 primes), `k = 1000`.  Statistics exclude `p = 419`, so `n = 35` per row.

| elem | ensemble | mean excess | rms | max excess (p) | primes with excess > 0 |
|---|---|---|---|---|---|
| 1 | arith m=19 | -0.000058 | 0.000236 | +0.000407 (449) | 14 |
| 1 | arith m=1 | -0.000080 | 0.000263 | +0.000671 (503) | 6 |
| 1 | SL3 random | -0.000144 | 0.000287 | +0.000579 (853) | 9 |
| 1 | perm random | -0.000122 | 0.000285 | +0.000790 (349) | 9 |
| 2 | arith m=19 | -0.000104 | 0.000439 | +0.001456 (337) | 14 |
| 2 | arith m=1 | -0.000136 | 0.000372 | +0.000885 (337) | 10 |
| 2 | SL3 random | -0.000078 | 0.000371 | +0.000663 (307) | 11 |
| 2 | perm random | -0.000099 | 0.000344 | +0.000970 (491) | 13 |

- **Element 3** (top edge against 5).  Mean `lmax - 5`: arith m=19 `-0.00038`, m=1 `-0.00031`,
  SL3 `-0.00030`, perm `-0.00036`.  Largest `lmax`: `5.00069` (337), `5.00063` (337), `5.00109` (853),
  `5.00022` (937).  The bottom sits at `-3.00000` in every ensemble, as the identity forces.
- **Element 4** (against the random permutations at the same `p`).  Mean `lmax`: arith m=19 `4.66311`,
  m=1 `4.66315`, SL3 `4.66318`, perm `4.66315`.  Largest `lmax`: `4.66439` (503), `4.66398` (617),
  `4.66428` (853), `4.66408` (503).
- **The `p = 419` transient.**  `A = a^19` has order 22 mod 419, so `A^2` and `B^2` have order 11.  The
  excesses there are: element 1 `+0.00279`; element 2 `+0.19721`; element 3 `lmax - 5 = +0.00277`;
  element 4 top `+0.00584` above the permutations.  Elements built from powers amplify the finite-order
  effect by two orders of magnitude.  Element orders tend to infinity along primes, so this is still
  consistent with strong convergence.

## Job 2: every degenerate principal series at once, `l^2_0(F_p^3 minus 0)`

`k = 800`, 13 split primes up to 211 (`N` up to `9.39e6`).  Each cell gives the excess for arith m=19 / SL3 random / perm random.

| p | elem 0 | elem 1 | elem 2 |
|---|---|---|---|
| 29 | +0.0100 +0.0016 -0.0000 | +0.0194 +0.0017 -0.0018 | +0.0515 +0.0028 -0.0028 |
| 41 | -0.0013 +0.0163 -0.0001 | +0.0044 +0.0288 -0.0005 | +0.0230 +0.0200 -0.0008 |
| 43 | +0.0078 +0.0005 -0.0009 | +0.0020 +0.0018 -0.0007 | +0.0101 +0.0105 -0.0010 |
| 71 | +0.0049 +0.0016 -0.0000 | +0.0027 +0.0004 +0.0005 | +0.0021 +0.0117 -0.0003 |
| 83 | +0.0006 +0.0011 -0.0003 | +0.0041 +0.0010 -0.0000 | +0.0041 +0.0030 -0.0001 |
| 97 | +0.0019 +0.0020 -0.0000 | +0.0012 -0.0001 +0.0000 | +0.0009 +0.0051 -0.0002 |
| 113 | +0.0013 +0.0009 -0.0000 | +0.0003 +0.0013 -0.0001 | +0.0024 +0.0013 +0.0000 |
| 127 | +0.0008 +0.0007 -0.0000 | +0.0019 +0.0008 +0.0000 | +0.0026 +0.0029 -0.0002 |
| 139 | +0.0006 +0.0007 -0.0001 | +0.0007 +0.0019 +0.0001 | +0.0013 +0.0007 -0.0001 |
| 167 | +0.0009 +0.0013 -0.0000 | +0.0002 +0.0003 -0.0000 | +0.0006 +0.0020 -0.0000 |
| 181 | +0.0024 +0.0018 +0.0000 | +0.0001 +0.0009 -0.0000 | +0.0022 +0.0014 +0.0000 |
| 197 | +0.0023 +0.0014 -0.0000 | +0.0017 +0.0010 +0.0000 | +0.0005 +0.0016 -0.0001 |
| 211 | +0.0010 +0.0006 -0.0000 | +0.0013 +0.0010 -0.0000 | +0.0014 +0.0010 +0.0001 |

- **Summary for `p >= 83`** (9 primes).  Mean excess, arith against SL3:
  - elem 0: `+0.00131` against `+0.00117`;
  - elem 1: `+0.00127` against `+0.00089`;
  - elem 2: `+0.00176` against `+0.00212`.

  The arithmetic pair exceeds the SL3 control at 5 of 9 primes for each element.
- **Why the positive excesses.**  The space splits into `p - 1` sectors of dimension `p^2+p+1`, pairwise
  complex conjugate.  The excess is the maximum over about `(p-1)/2` independent edges, each fluctuating
  at scale `(p^2)^(-2/3)`, and it decays with `p` in both ensembles.
- **Matched control.**  Random permutations of the same `N` do not split this way and give about 0.  They
  are not a matched control here; the SL3 pairs are.
- **Small primes.**  At `p <= 71` the arithmetic excesses reach `+0.05`.  These are small-`p` effects of
  short element orders, the same kind as `p = 419`; the SL3 control reaches `+0.029` at `p = 41`.

## Job 3: edge statistics at Tracy--Widom scale, `P^2(F_p)`, element 0

Every split prime `300 < p < 1000` except 419, `k = 1500`.  Arith m=19 and m=1 at each prime; three SL3 and
three permutation samples per prime.  Scaled edge `s = N^(2/3) (lambda - 2 sqrt 3)`, for the top
(`lambda = lmax`) and the bottom (`lambda = -lmin`) separately.

| ensemble | n | top: mean, sd, P(s > 0), max | bottom: mean, sd, P(s > 0), max | non-Ramanujan | mean raw excess, p >= 700 |
|---|---|---|---|---|---|
| arith m=19 | 35 | -0.967, 1.102, 0.17, +1.738 | -1.192, 1.065, 0.11, +2.206 | 0.29 | -0.000022 |
| arith m=1 | 35 | -0.974, 0.752, 0.09, +1.282 | -1.179, 0.890, 0.09, +1.129 | 0.17 | -0.000062 |
| SL3 random | 105 | -1.095, 0.894, 0.12, +1.193 | -1.024, 0.995, 0.13, +1.668 | 0.24 | -0.000069 |
| perm random | 105 | -1.196, 1.024, 0.11, +1.270 | -1.052, 0.972, 0.13, +1.431 | 0.22 | -0.000061 |

- **The ensembles agree.**  The standard error of an arithmetic mean is about `0.17`, and the
  arithmetic and random means differ by at most `0.23`.
- **Shortfall.**  At `N ~ 1e5-1e6`, `k = 1500` leaves a shortfall comparable to `N^(-2/3)`.  So the
  negative means are partly shortfall, and the non-Ramanujan fractions are lower bounds.  The comparison
  is matched in `N` and `k`.

## Interpretation

1. **Random-like everywhere tested.**  The certified thin pair's congruence Schreier graphs match
   Haar-random `SL_3(F_p)` pairs at the resolution reached (`~1e-4` absolute, `~N^(-2/3)` relative).
   That covers five group-ring elements, including nonlinear ones with exact regular spectra; the `P^2`
   sector at `p < 1000`; and every degenerate principal series at `p <= 211`.  There is no systematic
   excess.
2. **Not exactly Ramanujan.**  At 17--29% of primes the `P^2` graph has a genuine eigenvalue above
   `2 sqrt 3`, the same share as the random ensembles.  So nothing Hecke-like forces exact temperedness.
   An outlier mechanism, if one exists, is not visible at this scale.
3. **The one systematic effect is finite order** (`p = 419`), amplified by elements built from powers.
4. **Not tested.**  Cuspidal sectors at scale, `p > 1000` for nonlinear elements, and other algebras.
