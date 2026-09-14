---
rg: 2
id: thompson-f-p22-explicit-pair-degree-bound-wiedemann-proof
kind: route
title: Split by degree and by inert letter tails, then certify injectivity of each finite block by a full-degree Wiedemann characteristic polynomial
target: thompson-f-p22-explicit-pair-no-common-multiple-below-degree-9
requires: []
artifacts:
  - research/artifacts/hl-thompson-f-2026-09-13.md
---

Notation as in the claim. `K[F]` has no zero divisors (`F` is left-orderable). So a nonzero pair `(u, v)`
with `a u = b v` has `u != 0` and `v != 0`.

**Step 1 (degree splitting).** `a` and `b` are homogeneous of degree 2. So `a u = b v` holds degree by
degree: `a u_D = b v_D` for every homogeneous component. It suffices to show that for each `D <= 8` the
map `A_D : K[M_D]^2 -> K[M_(D+2)]`, `(u, v) -> a u - b v`, is injective.

**Step 2 (inert letter tails).** For `s = x_(s_1) x_(s_2) ∈ S` and `y ∈ M_E`, compute `s y` by inserting
`s_2` and then `s_1` (left insertion: the letters of the word are unchanged and the inserted letter grows
by one per letter passed).
- The inserted letters are `<= s_2 + E` and `<= s_1 + E + 1`, so `<= R(E) = E + 3`, since `s_1 <= 2`
  and `s_2 <= 3`.
- The insertion never passes a letter `> R(E)`.

Now fix `T >= R(E)` and write `w ∈ M_D` as `w = w_low w_high`, where `w_high` consists of the letters
`> T` and `w_low ∈ M_E` for some `E`.
- Then `s w = (s w_low) w_high`, and the letters `> T` of `s w` are exactly `w_high`.
- So `A_D` is block diagonal over the tails `w_high`. Each block is a copy of `A_E` restricted to words
  with letters `<= T`.

Applying this with `T = R(E)` repeatedly, a nonzero kernel vector of `A_D` produces a nonzero kernel
vector of `A_E` restricted to `M_(E, E+3)` for some `E <= D`. So it suffices to show that `A_E` is
injective on `K[M_(E, E+3)]^2` for `E = 1, ..., 8`.

**Step 3 (reduction to `F_p`).** `A_E` on `M_(E, E+3)` is a matrix with integer entries `α_s`, `-β_s`.
If its reduction modulo `p = 2^61 - 1` has full column rank `N = 2|M_(E,E+3)|`, some `N × N` minor is
nonzero modulo `p`, hence nonzero over `Z`. Then the matrix has full column rank over every field of
characteristic 0 and every field containing `F_p`.

**Step 4 (certificate over `F_p`).** `experiments/thompson-f/hl/genwied2.cpp`, run on MSI with
`seed = 1`, prints the coefficients above. For each `E` it builds `A_E` over `F_p` from the monoid normal
forms (`R` rows), a random matrix `C` with 4 nonzero entries per row (`N × R`), and `B = C A_E`
(`N × N`). It computes `s_i = w^T B^i x` for `i < 2N + 2` with random `w, x`, and runs Berlekamp–Massey.
- The returned minimal polynomial `f` of the sequence divides the minimal polynomial of `B`, which
  divides the characteristic polynomial of `B`, of degree `N`.
- In every case below `deg f = N` and `f(0) != 0`. So `f` is the characteristic polynomial and
  `det B != 0`.
- Since `A_E z = 0` implies `B z = 0`, `A_E` is injective.

| E | `|M_(E,E+3)|` | rows | N | `deg f` | `f(0) != 0` |
|---|---|---|---|---|---|
| 1 | 5 | 28 | 10 | 10 | yes |
| 2 | 21 | 99 | 42 | 42 | yes |
| 3 | 84 | 361 | 168 | 168 | yes |
| 4 | 330 | 1338 | 660 | 660 | yes |
| 5 | 1287 | 5013 | 2574 | 2574 | yes |
| 6 | 5005 | 18931 | 10010 | 10010 | yes |
| 7 | 19448 | 71929 | 38896 | 38896 | yes |
| 8 | 75582 | 274638 | 151164 | 151164 | yes |

**Provenance of the runs.**
- `E = 1..5`: the coefficient-printing variant `genwied2.cpp` (md5 `ffddcb555ec921f29065353117532871`).
- `E = 6, 7, 8`: `genwied.cpp` (md5 `5c5da9131183527b9627a0ae3794d11c`), MSI job 732629 (tasks 4, 5, 6;
  `E = 8` took 3124 s). It differs from `genwied2.cpp` only by the print line, and draws the same
  coefficients from the same seed.
- Output lines are in `experiments/thompson-f/hl/wied-runs.txt`.

**Calibration.** On singular cases the same program recovered exact kernel vectors, i.e. nonzero `z` with
`A z = 0` checked directly, for random pairs of linear forms in `x_0, ..., x_m` at degree `m`
(`m = 3, 4, 5`). It certified injectivity in all lower degrees there. The row counts agree with
`experiments/thompson-f/doubling_flow.cpp` wherever both were run (`X_3`, `D = 5`: 2793; `X_4`,
`D = 7`: 72579). Details are in the artifact.
