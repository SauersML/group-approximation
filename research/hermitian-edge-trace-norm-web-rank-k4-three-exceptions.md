---
rg: 2
id: hermitian-edge-trace-norm-web-rank-k4-three-exceptions
kind: claim
title: The Hermitian edge trace-norm inequality holds at the rank inequality of the web C_n^4 for every n >= 10 except n = 13, 14, 19
artifacts:
  - research/hermitian-edge-trace-norm-web-rank-k4-three-exceptions-windows.md
  - experiments/hermitian-edge-trace-norm-web-k4-2026-09-18/README.md
  - experiments/hermitian-edge-trace-norm-web-k4-2026-09-18/k5a.log
  - experiments/hermitian-edge-trace-norm-web-k4-2026-09-18/k5b.log
  - experiments/hermitian-edge-trace-norm-web-k4-2026-09-18/web_clique_lists_k4.log
distinct_from:
  hermitian-edge-trace-norm-web-rank-k4-six-exceptions: that uses c_5 >= 7.168 and leaves n = 12, 13, 14, 18, 19, 24 open; this uses c_5 >= 7.2169 and closes n = 12, 18, 24.
  hermitian-edge-trace-norm-clique-k5-margin: that is c_5 >= 7.0857; the stronger c_5 >= 7.2169 is proved inside this claim's route and is used only for the webs.
---

**ESTABLISHED (computer-assisted, exact-rational SDP certificates plus exact rational arithmetic;
unreviewed, not Lean-verified; route `hermitian-edge-trace-norm-web-rank-k4-three-exceptions-windows`).**

**Theorem.** Let `C_n^4` be the web on `Z_n`, where `i ~ j` iff the cyclic distance of `i` and `j`
is in `1..4`. Let `n >= 10` with

```text
n  not in  {13, 14, 19} .
```

Then every admissible `C` on `C_n^4` satisfies `||C||_1 >= sqrt3 (n - floor(n/5))`. (Admissible
means Hermitian, zero diagonal, zero on non-edges, and `|C_ij| >= 1` on edges.)

The input is `c(K_5) >= 7.2169`: every Hermitian `5 x 5` matrix with zero diagonal and
off-diagonal moduli at least `1` has trace norm at least `7.2169`.

- This is `0.27%` below the numerical minimum `5 + sqrt5 = 7.2361`.
- It is just above `50 sqrt3/12 = 7.21688`, the value that `n = 12` needs.

**Why it matters.** This settles `n = 12, 18, 24` of `hermitian-edge-trace-norm-web-rank-k4-six-exceptions`.
Five-vertex clique windows cannot do more.

- Even the true value `c_5 = 7.2361` leaves `n = 13, 14, 19` open, because
  `n (c_5 - 4 sqrt3) < sqrt3 (n mod 5)` there.
- Those three values need a window with more vertices. For example, `c(P_7^4) >= 6 sqrt3 = 10.3923`
  would close them all. The numerical minimum of `c(P_7^4)` is `10.6873`.

## Attempts

- 2026-09-18 (w9-078): proved via five-vertex clique windows and a branch-and-bound for
  `c(K_5) >= 7.2169` (route `hermitian-edge-trace-norm-web-rank-k4-three-exceptions-windows`).
  - The branch-and-bound adds two proved reductions to `graphbb_r.py`: a pinching cut on large
    moduli, and a fundamental domain for `S_5 x conj x neg` on the ten triangle phases.
  - It closes in 20027 solves, about 19 minutes on a machine at load 28.
  - `P_7^4` windows for `n = 13, 14, 19`, at target `10.3924`: sampling at 30 centres says a box
    closes with one solve only up to phase half-width about `0.7`.
    - That is about `1.1e8` boxes over the twelve free phases.
    - The automorphism group is `S_3 x Z_2`, so `conj` and `-K` give at most a factor `48`.
    - Not run: this is CPU-weeks here.
  - Obstruction: the fixed-`Z` bound keeps only `cos h` of each edge term on an arc of half-width
    `h`. So a box closes only if `h <= arccos(10.3924/||C||_1)`, which is about `0.7` for typical `C`.
    A cheaper route needs a bound that is not linear in `K` on a box, or a reduction of the phase
    space by more than the symmetry group.
