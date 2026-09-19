# Robust-SDP branch-and-bound for webs (lane w8-078, 2026-09-18)

Supports `research/hermitian-edge-trace-norm-web-rank-k3-n11-p6cube-windows.md` (`c(P_6^3) >= 8.5028`).
It also supports `research/hermitian-edge-trace-norm-web-rank-k4-six-exceptions-windows.md`
(`c(K_5) >= 7.168`).

## graphbb_r.py

This is `experiments/hermitian-edge-trace-norm-webs-2026-09-18/graphbb.py` with one change: how the
candidate dual matrix `Z` for a phase box is found. Usage is the same:
`graphbb_r.py GRAPH TARGET T n0 a_lo a_hi checkpoint.pkl`.

- **graphbb.py.** Solves the SDP `max sum_e 2 Re(Z_ji e^{i th_e})` over `-I <= Z <= I` with all
  terms `>= 0`, at the box centre.
- **graphbb_r.py.** Solves one SDP for the whole box: maximise `sum_e s_e` over `-I <= Z <= I` and
  `0 <= s_e <= 2 Re(Z_ji e^{i lo_e})`, `s_e <= 2 Re(Z_ji e^{i hi_e})`. On an arc of length `< pi`, a
  sinusoid that is `>= 0` at both ends has its minimum at an end. So the optimum is a lower bound
  that holds on the whole box, not just at its centre. Boxes of width `>= 3` are bisected without a
  solve.

Everything that makes the result a proof is unchanged, line for line:

- `rational_Z`: scale by `1 - 1e-6`, round to Gaussian rationals with denominator `2^30`, make
  Hermitian;
- `pd_exact`: exact Fraction pivots of `I - Z` and `I + Z`;
- `box_bound`: an edge-separable bound over moduli `[1, T]` and the phase box, with exact cosine
  ranges and outward padding;
- the modulus cut `2T >= TARGET`.

A box counts as closed only if `box_bound` of the exactly checked rational `Z` (its own, or its
parent's) is `>= TARGET`.

**Speed.** At `8.5028` on the test box `box03.json` (half-width `0.3` around the numerical minimiser),
the robust version closes 10 boxes with 19 solves in 2 s. At `8.3139`, `graphbb.py` needed 100 boxes
and 150 solves in 21 s. On `K_5` at `7.167`, a box of half-width `0.4` around the minimiser closes
with 53 solves. On `P_7^4` (12 free phases) at `10.3923`, it closes with 67 solves.

## Runs

`lane.sh GRAPH TARGET T N0 TAG [A_LO A_HI]` repeats `nice -n 10 timeout 1200 graphbb_r.py ...` and
resumes from `ck_TAG.pkl` until `ALL CLOSED` or `FAIL` appears in `TAG.log`. Single-threaded.

- `p6cube_hi.log`: `W12/1.2.3:0,1,2,3,4,5 8.5028 4.26 3 0 pi/2`, which is `P_6^3` with the phase
  of edge `12` in `[0, pi/2]`. `ALL CLOSED`: 40647 boxes, 78735
  solves, 4408 s in total over several tries. The numerical minimum of `c(P_6^3)` is `8.6413`.
- `k5_a.log`: `lane.sh K5 7.168 3.6 3 k5_a 0 pi/4`. `ALL CLOSED`: 10878 boxes, 20925 solves, 1340 s
  in total over two tries (the counts carry over through the checkpoint).
- `k5_b.log`: `lane.sh K5 7.168 3.6 3 k5_b pi/4 pi/2`. `ALL CLOSED`: 12600 boxes, 24339 solves, 1463 s
  in total over two tries (the counts carry over through the checkpoint).
- Together, `c(K_5) >= 7.168` with the first free phase (edge `12`, star tree at `0`) in `[0, pi/2]`,
  in 23478 boxes and 45264 solves. `2T = 7.2 >= 7.168`. The numerical minimum is `5 + sqrt5 = 7.2361`.
