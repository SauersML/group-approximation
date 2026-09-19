# Web C_n^4 at n = 13, 14, 19: window obstruction, the G_6 certificate for n = 19, and the cost of P_7^4 (w10-078, 2026-09-19)

These scripts support `research/hermitian-edge-trace-norm-web-k4-small-window-limits.md` and (`g6s.log`) `research/hermitian-edge-trace-norm-web-rank-k4-n19.md`.
Run everything single-threaded, for example `OMP_NUM_THREADS=1 nice -n 10 python3 ...`.

## The proof part

`cover.py MAXSIZE RESTARTS` (run as `cover.py 6 4`, output `cover6.log`) does the following:

1. It lists the isomorphism classes of the induced subgraphs of `C_13^4`, `C_14^4` and `C_19^4`
   on at most `MAXSIZE` vertices. There are 91 classes for `MAXSIZE = 6`.
2. For each class it builds an explicit admissible matrix, with every edge modulus at least `1`
   (it rescales and asserts this).
3. It prints the trace norms and the largest density `||C_W||_1 / |W|`.

The needed densities `sqrt3 (n - floor(n/5)) / n` are `1.46558`, `1.48461` and `1.45857`. The
log shows two things:

- Only `G_6`, the window `{0, 1, 2, 3, 4, 6}`, exceeds any of them. Its density is `1.46844`.
- The next density is `1.44805`, from `K_5`.

## Seven-vertex windows (numerics)

- `cover7.py 13 2` (output `cover7.log`) bounds `c` for the `46` seven-vertex window classes with
  at least `13` edges. It uses 2 starts each, so the values are local minima.
- `member7.py` (output `member7.log`) lists which of these classes occur in each of `C_13^4`,
  `C_14^4` and `C_19^4`, sorted by density.

## The numerics part (not needed for the claim)

- `so2.py` builds `P_7^4` with the tree gauge (tree `(0,1) (0,2) (0,3) (0,4) (1,5) (2,6)`, 12 free
  phases, `T = 2.46`). It defines the linear fixed-`Z` box bound `linbound` and a
  first-plus-second-order prototype, and compares them with the true box minimum.
- `so2b.py` is a Gram-matrix variant of the second-order bound. `so2c.py` is the rotation-type
  `Z = Z0 + D1 - Z0 D1^2 / 2`. Both are weaker than `linbound`.
- `frac.py` uses `rsdp_mod.py`, the robust SDP of `fastbb.py` (w9-078) extracted as a class. It
  reports, for 40 random boxes of half-width `h`, how many close with the sign `Z` and with the
  SDP `Z`. The output is `frac.log`, if present; the numbers are also quoted in the claim.
- `vbb.py w k TARGET lo1 hi1 [MAXB]` is a vectorised branch-and-bound prototype with the same
  certificate as `fastbb.py`. It does not use exact rational checking or the symmetry reduction.
  Its settings come from the environment: `HS` (half-width below which the SDP is tried),
  `WMIN` and `PRINTN`. `vbb_p7_trial.log` is the start of a run on `P_7^4` at `6 sqrt3`, which
  shows that the split rule dives too deep.
- `freemin.py` minimises `||C||_1` on `P_7^4` with some edges freed (any complex value). Its
  output `free1.log` gives the one-edge values; the best, `10.429`, is `0.35%` above `6 sqrt3`.

## The window `G_6` and the certificate for `n = 19`

- `g6min.py 4` (output `g6min.log`) minimises `||C||_1` on `G_6` from 4 seeds of 10 starts. All
  four give `c(G_6) <= 8.8107`. The best is `8.810635`.
- A certificate of `c(G_6) >= 8.7515` would prove the rank inequality for `C_19^4`, because
  `(19/6) 8.7515 = 27.7131 >= 16 sqrt3 = 27.7128`. A certificate of `c(G_6) >= 8.7935` would do
  the same for `C_13^4`.
- The run uses `fastbb.py` and `run.sh` of
  `experiments/hermitian-edge-trace-norm-web-k4-2026-09-18/` (w9-078), unchanged:

  ```text
  SYM='3.4+4.5-3.5<4.5;4.5<3.5;0.3<1.3' ROOT=2 FIRST=0-1 \
    bash run.sh g6s 'W13/1.2.3.4:0,1,2,3,4,6' 8.7515 2.376 0 1.5707963267948966 40
  ```

- In the `W13` labels, the window vertex `6` is `G_6`'s sixth vertex, adjacent to `2, 3, 4`. With
  root `2`, the tree edges are the 5 edges at `2`, which leaves `13 - 5 = 8` free phases.
- The pinching cut is `2T + MCUT >= TARGET`, which gives `T = 2.376`.
  - If some `|C_ij| > T`, pinch into `{i, j}` and the other four vertices.
  - Those four vertices always contain two disjoint edges of `G_6`. Each edge contributes at
    least `2`, so `MCUT = 4`.
- **Why the symmetry reduction is valid.**
  - `Aut(G_6)` is `Z_2 x S_3`: swap `0` and `1`, and permute `{2, 3, 4}`.
  - A diagonal unitary gauge fixes the tree phases to `0`, and the triangle phase sums
    `u(abc) = theta_ab + theta_bc + theta_ca` are gauge invariant.
  - Composing with an automorphism permutes the triangles, so one can assume
    `u(345) <= u(245) <= u(235)` and `u(023) <= u(123)`. These are the SYM constraints of
    `fastbb.py`.
  - Complex conjugation and the sign change `C -> -C` keep `||C||_1` and admissibility. Together
    they reduce the phase of the edge `01` to `[0, pi/2]`.
- **Result.** The run closed. The last line of `g6s.log` reads `ALL CLOSED`, with 176838 boxes:
  - 7134 dropped by symmetry;
  - 5636 closed by the parent `Z`, 819 by the centre sign `Z` and 170383 by the robust SDP;
  - 353261 solves, and a smallest half-width of `0.065`.
  - It took 17716 s of wall time, on a machine at load about 26 on 4 cores, in 1200 s chunks that
    resume from the checkpoint. The `resumed` lines mark the chunks.
- So `c(G_6) >= 8.7515`, which proves the rank inequality of `C_19^4`. This is
  `research/hermitian-edge-trace-norm-web-rank-k4-n19.md`.
