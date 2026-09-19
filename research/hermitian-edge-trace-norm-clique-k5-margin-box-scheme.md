---
rg: 2
id: hermitian-edge-trace-norm-clique-k5-margin-box-scheme
kind: route
title: Rerun the K5 box-certificate scheme with TARGET 7.0857 and modulus cap T = 3.55 on the same 16 symmetry slices
target: hermitian-edge-trace-norm-clique-k5-margin
requires: []
artifacts:
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/graphbb.py
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/k5hilane.sh
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/k5hi_runs.log
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/README.md
  - research/hermitian-edge-trace-norm-clique-inequality-k5-proof.md
---

A computer-assisted proof. It is unreviewed and not Lean-verified. Lane w7-078, 2026-09-18.

**Theorem.** Every Hermitian `5 x 5` `C` with `C_ii = 0` and `|C_ij| >= 1` (`i != j`) has
`||C||_1 >= 7.0857`.

The mathematics is Steps 1–3 of `hermitian-edge-trace-norm-clique-inequality-k5-proof` with two
constants changed. Only the constants and the program differ.

## Step 1. Gauge and large moduli

Gauge the star at vertex `0` to be real and positive. The other six entries are
`t_ij e^{i theta_ij}` with `t_ij >= 1`. If some modulus exceeds `T = 3.55`, the `2 x 2` compression
gives `||C||_1 > 2T = 7.1 > 7.0857`. So assume all ten moduli lie in `[1, 3.55]`.

## Step 2. Symmetry reduction

As in the `K_5` proof: `C -> -D C D` with `D = diag(-1, 1, 1, 1, 1)` shifts every free phase by
`pi`, and `C -> conj(C)` negates them. Both preserve the trace norm and the gauge. So the first
free phase `theta_12` (vertices numbered from `0`) can be taken in `[0, pi/2]`, cut into the 16
slices `[i pi/32, (i+1) pi/32]`. The other five phases range over `[0, 2 pi)^5`.

## Step 3. Box certificates

`graphbb.py` is the graph version of `cliquebb.py`. The graph `K5` has the same gauge (a BFS tree,
here the star at `0`) and the same certificate. For a box of phases it solves the SDP
`max tr(ZC)`, `-I <= Z <= I`, at the centre. It scales `Z` by `1 - 10^-6` and rounds it to Gaussian
rationals. It checks `I - Z > 0` and `I + Z > 0` exactly with `Fraction` pivots. It then bounds
`tr(ZC) = sum_{i<j} t_ij 2 Re(Z_ji e^{i theta_ij})` below over the box and over `t_ij in [1, T]`.
That bound is edge-separable and uses outward-rounded cosine ranges. A box whose bound reaches
`TARGET = 7.0857` is closed. Otherwise it is bisected on its widest side, trying the parent's `Z`
first. A box narrower than `10^-4` would print `FAIL`.

## Step 4. The run

`k5hilane.sh 16 <i>` runs `graphbb.py K5 7.0857 3.55 3 lo hi ck.pkl` on slice `i` from a `3^6`
grid. It resumes from a checkpoint after each 1200 s try. All 16 slices print `ALL CLOSED`, and
none prints `FAIL`. `k5hi_runs.log` collects the final line of each slice and the totals: 938614 boxes,
1327413 SDP solves, smallest box-centre value `7.255450` (slice 7), 45002 s of CPU time in all. ∎
