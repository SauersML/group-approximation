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

Numerical context: the minimum over the torus of `min_t ||K||_1` is `2 + 2 sqrt3 = 5.4641`, at flux
`(2pi/3, 2pi/3, 2pi/3)`, found by a `12^3` grid of SDPs. The target is `3 sqrt3 = 5.1962`.
