# Weighted windows for the web C_n^4 at n = 13, 14 (lane w11-078, 2026-09-19)

Unreviewed, not Lean-verified. `c(H, w)` is the minimum of `||C||_1` over Hermitian `C` on `H`
(zero diagonal, zero on non-edges) with `|C_ij| >= sqrt(w_i w_j)` on edges; `c(H) = c(H, 1)`.
`W14/1.2.3.4:S` is the subgraph of `C_14^4` induced on the list `S`, re-indexed `0, 1, ...`.

## The certificate (the only file a proof depends on besides `fastbbw.py`)

- `k5p.log`: `fastbbw.py` on `H = W14/1.2.3.4:0,1,2,3,4,8` (the clique `K_5` on `0..4` plus a
  pendant vertex `5 = 8` at `4`) with weights `w = (3/4, 3/4, 3/4, 3/4, 1, 1/5)`, target `6.23539`.
  Its final line reads `ALL CLOSED`. Command, in this directory:

```text
SYM='0.1<0.2,0.3,1.2,1.3,2.3;0.2<0.3,1.2,1.3' ROOT=4 FIRST=0-1 CKEVERY=200 \
  bash runw.sh k5p 'W14/1.2.3.4:0,1,2,3,4,8' 6.23539 3/4,3/4,3/4,3/4,1,1/5 0 1.5707963267948966
```

  The first 900 s were the pilot (`pilotK.log`); the run resumed from its checkpoint, so `k5p.log`
  starts with the pilot's lines and its counters include them. Final line: `ALL CLOSED`, 15134
  boxes (1634 dropped by symmetry), 29653 solves, 2061 s of wall time.

## Programs

- `fastbbw.py`: vertex-weighted version of
  `experiments/hermitian-edge-trace-norm-web-k4-2026-09-18/fastbb.py` (w9-078). Its header lists every change: the dual `Z'` is checked
  exactly against `-D < Z' < D` (`D = diag w`), the modulus cut is per edge with weighted packings, and full
  circles split into 4 pieces (search only). Calibration: on `K3` with weights `1, 2, 3` it closes
  target `6.6` and fails at `6.64`, while `c(K3, w) = 2 sqrt(2 + 3 + 6) = 6.6332`.
- `runw.sh`: the resume loop (as `run.sh` of the 2026-09-18 directory, with `fastbbw.py` and `nice -n 19`).
- `wdens.py`, `wcheck.py`: numerical upper bounds on `c(G[W], w)` (BFGS, analytic gradient).
- `wopt.py`: the weight search. By the envelope theorem `d c / d w_i = |C|_ii / w_i` at the
  minimiser `C`, so the density `c(w)/|w|` is stationary when `w` is proportional to `diag |C|`;
  `wopt.py` iterates `w <- (w + diag|C| / rho) / 2`.
- `w7min.py`: numerical unweighted `c` of a window.

## Numerics (upper bounds, not proofs)

| window (in `C_14^4`) | phases | weights | density `c / sum w` | needed n=14 / n=13 |
|---|---|---|---|---|
| `{0..5, 8}` unweighted | 10 | 1 | `10.4941/7 = 1.4992` | `1.48461 / 1.46558` |
| `{0..5, 8}` | 10 | `wopt_w7.log` | `1.5261` | |
| `{0,1,2,3,4,8}` | 6 | `(3/4 x4, 1, 1/5)` | `6.32817/4.2 = 1.50671` | |
| `G_6 = {0,1,2,3,4,6}` | 8 | `wopt_g6.log` | `1.4867` | |
| `{0..5}`, `{0,1,2,3,4,7}`, `{0,1,2,3,5,6}` | | `wopt6_<window>.log` | `1.447, 1.456, 1.465` | |

The table value `c({0..5, 7}) <= 10.700` of the small-window tabulation is a bad local minimum;
`w7min_7.log` finds `10.4799`.

## Pilots (why the brief's unweighted run was not made)

- `pilotA.log`: unweighted `c({0..5,8}) >= 6 sqrt3` (target `10.39231`, `fastbb.py`): after 16000 solves
  the closed volume is `4.1e-4` of the (symmetry-reduced) domain; linear extrapolation about `4e7`
  solves, i.e. months at the ~18 solves/s this loaded machine gives.
- `pilotB.log`: the same at the `n = 13` target `10.2591`: `1.2e-3` after 17000 solves.
- `pilotW.log`, `pilotW4.log`: weighted `{0..5, 8}` at the `n = 14` target `7.48989` (margin 2.8%),
  3-way and 4-way splits: `3.2e-3` after 13000 and `3.9e-3` after 17000 solves (~`4e6` solves).
- `pilotK.log`: weighted `{0,1,2,3,4,8}` (6 phases, margin 1.49%): `0.24` after 9000 solves in
  800 s. This is the run that was made.
