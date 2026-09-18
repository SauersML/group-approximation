---
rg: 2
id: hermitian-edge-trace-norm-clique-inequality-k5-proof
kind: route
title: The K4 box-certificate scheme on the six-torus of K5 phases, reduced by a sign-and-conjugation symmetry to a quarter circle and covered in 16 slices
target: hermitian-edge-trace-norm-clique-inequality-k5
requires: []
artifacts:
  - experiments/hermitian-edge-trace-norm-clique-small-m-2026-09-18/cliquebb.py
  - experiments/hermitian-edge-trace-norm-clique-small-m-2026-09-18/k5lane.sh
  - experiments/hermitian-edge-trace-norm-clique-small-m-2026-09-18/k5_partial_runs.log
  - experiments/hermitian-edge-trace-norm-clique-small-m-2026-09-18/README.md
---

A computer-assisted proof. It is unreviewed and not Lean-verified. The mathematics is Steps 1–4 of
`hermitian-edge-trace-norm-clique-inequality-k4-proof`, which are written for general `m`, plus the
symmetry reduction below. The machine part is `cliquebb.py` at `m = 5`, whose certificates are checked
in exact rational arithmetic. Lanes w6-078 (slices 0, 1, 2, 6, 7, 11, 12) and w7-078 (the other nine),
2026-09-18.

**Theorem.** Every Hermitian `5 x 5` matrix `C` with `C_ii = 0` and `|C_ij| >= 1` (`i != j`) has
`||C||_1 >= 4 sqrt3`.

## Step 1. Gauge and large moduli

These are Steps 1–2 of the `K_4` proof with `m = 5` and `T = 3.47`, where `2T = 6.94 > 4 sqrt3 = 6.9282`.
- Conjugating by a diagonal unitary makes the star `C_1j = t_1j >= 1` real.
- The six other entries are `t_ij e^{i theta_ij}`, `2 <= i < j <= 5`, with `t_ij >= 1`.
- If some modulus `|C_ij| > T` (star entry or not), then the `2 x 2` principal compression on `{i, j}`
  gives `||C||_1 >= 2 |C_ij| > 6.94`, since compression does not increase the trace norm. So assume
  all ten moduli lie in `[1, T]`.

## Step 2. Symmetry reduction

Both maps below preserve the trace norm, the zero diagonal, the moduli, and the reality of the star.
- `C -> -D C D` with `D = diag(-1, 1, 1, 1, 1)` shifts every free phase by `pi`.
- `C -> conj(C)` negates every free phase.

Given `theta_23 in [0, 2 pi)`: if `theta_23 >= pi`, apply the first map. If the result is in
`(pi/2, pi)`, apply the second, then the first. This brings `theta_23` into `[0, pi/2]`, and the
other five phases stay in `[0, 2 pi)^5`. The quarter circle is cut into the 16 slices
`[i pi/32, (i+1) pi/32]`, `i = 0..15`.

## Step 3. Box certificates

These are Steps 3–4 of the `K_4` proof. For a box of phases, `cliquebb.py` does the following:
1. It solves the SDP `max tr(ZK)` subject to `-I <= Z <= I` at the box centre.
2. It scales the solution by `1 - 10^{-6}`, rounds it to Gaussian rationals with denominator `2^30`,
   and checks `I - Z > 0` and `I + Z > 0` in exact arithmetic (Gaussian elimination pivots).
3. It uses `||C||_1 >= tr(ZC) = sum_{i<j} t_ij g_ij(theta)`. The exact minimum over the box and over
   `t_ij in [1, T]` is edge-separable, and the cosine ranges are computed with outward rounding.

A box whose bound reaches `TARGET = 6.9282033 > 4 sqrt3` is closed. Otherwise it is bisected along
its widest side. The parent's `Z` is tried on each child first.

## Step 4. The run

`k5lane.sh 16 <i>` runs slice `i` from an initial grid of `3^6` boxes, resuming from checkpoints.
All 16 slices print `ALL CLOSED` (`k5_partial_runs.log`). No `FAIL` (box narrower than `10^{-4}`)
occurred. Per slice there were 28,538–31,852 closed boxes and 40,994–45,709 SDP solves, taking
827–1,552 s on one core. The smallest SDP value at any box centre was `7.2555` (slice 7). The
numerical minimum is `5 + sqrt5 = 7.236`. In slice 8 a launcher mistake resumed the run twice
concurrently from one checkpoint; the two deterministic runs printed identical box and solve counts,
and the log says so. ∎

With `hermitian-edge-trace-norm-clique-inequality-k4` and `-large-m`, this completes
`hermitian-edge-trace-norm-clique-inequality-by-size`, so the uniform clique inequality holds for every `m`.
