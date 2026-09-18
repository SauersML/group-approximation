# Clique inequality at m = 4 (and m = 5): flux-torus branch-and-bound (lane w6-078, 2026-09-18)

This supports `research/hermitian-edge-trace-norm-clique-inequality-k4-proof.md`.

## Files

`cliquebb.py` is the whole proof machine. Run it as

```text
python3 cliquebb.py m a_lo a_hi tag n0 [checkpoint.pkl]
```

It covers the torus of free phases (after gauging the star at vertex 1 to be real) by boxes.
- The first free phase ranges over `[a_lo, a_hi]` and the others over `[0, 2 pi)`, starting from an
  `n0^F` grid.
- On each box it tries a certificate `Z`: first the parent's, otherwise the SDP dual optimiser at the
  box centre (cvxpy + Clarabel).
- `Z` is rounded to Gaussian rationals, and `-I < Z < I` is checked exactly with `Fraction` pivots.
- It then evaluates the exact separable minimum of `tr(ZK)` over the box and over `t in [1, T]^E`,
  padded outward.
- A box is closed when that minimum is `>= TARGET > sqrt3 (m-1)`; otherwise it is bisected.
- The run prints `ALL CLOSED` only if every box is closed. The optional checkpoint makes long runs
  resumable.

`k5lane.sh` runs `m = 5` in slices of the first phase, with checkpoints.

## Results

| log | run | outcome |
|---|---|---|
| `k4_full_torus.log` | `m = 4`, whole torus `[0, 2pi)^3`, no symmetry used, `n0 = 4` | ALL CLOSED: 584 boxes, 740 SDP solves, smallest half-width 0.196, 12 s |
| `k5_partial_runs.log` | `m = 5`, `n0 = 3`, first phase in slice `[i pi/32, (i+1) pi/32]` for every `i = 0..15` (all 16 slices of `[0, pi/2]`), other five phases over `[0, 2pi)^5` | each ALL CLOSED: 28,538-31,852 boxes and 40,994-45,709 SDP solves per slice, 827-1,552 s per slice; smallest box-centre value 7.2555 (target 6.928) |
| `k5_partial_runs.log` | `m = 5`, `n0 = 3`, first phase in slice `[i pi/32, (i+1) pi/32]` for `i = 0, 1, 2, 6, 7, 11, 12` (7 of the 16 slices of `[0, pi/2]`), other five phases over `[0, 2pi)^5` | each ALL CLOSED: 28,538-31,685 boxes and 40,994-45,402 SDP solves per slice, 943-1,040 s per slice; smallest box-centre value 7.255 (target 6.928) |

Numerical context: the minimum over the torus of `min_t ||K||_1` is `2 + 2 sqrt3 = 5.4641`, at flux
`(2pi/3, 2pi/3, 2pi/3)`, found by a `12^3` grid of SDPs. The target is `3 sqrt3 = 5.1962`.

**m = 5 status: complete.** Every slice is certified; this proves
`research/hermitian-edge-trace-norm-clique-inequality-k5.md` (route `-k5-proof`). Lane w6-078 ran slices
`0, 1, 2, 6, 7, 11, 12`, and lane w7-078 ran the other nine with
**m = 5 status.** Slices `3, 4, 5, 8, 9, 10, 13, 14, 15` are not yet certified. To finish, run

```text
./k5lane.sh 16 3 4 5 8 9      # lane A
./k5lane.sh 16 10 13 14 15    # lane B
```

The lanes resume from their checkpoints after the 1200 s per-try wall limit. In slice 8, two resumed
copies ran concurrently from one checkpoint by a launcher mistake; being deterministic they print
identical counts, and the log marks this. The symmetry reduction to `theta_23 in [0, pi/2]` is explained in
`research/hermitian-edge-trace-norm-clique-inequality-k5-proof.md`. Slice 0 was run by an earlier
Each slice takes about 16 minutes on one core. The lanes resume from their checkpoints after the
1200 s per-try wall limit. The symmetry reduction to `theta_23 in [0, pi/2]` is explained in
`research/hermitian-edge-trace-norm-clique-inequality-k5.md`. Slice 0 was run by an earlier
launcher; it used the same algorithm without checkpoints, and its log tag is `s0`.
