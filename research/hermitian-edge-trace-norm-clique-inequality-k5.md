---
rg: 2
id: hermitian-edge-trace-norm-clique-inequality-k5
kind: claim
title: The clique inequality on K5 - a Hermitian 5x5 matrix with zero diagonal and off-diagonal moduli at least 1 has trace norm at least 4 sqrt3
artifacts:
  - research/hermitian-edge-trace-norm-clique-inequality-k5-proof.md
  - experiments/hermitian-edge-trace-norm-clique-small-m-2026-09-18/README.md
  - experiments/hermitian-edge-trace-norm-clique-small-m-2026-09-18/cliquebb.py
  - experiments/hermitian-edge-trace-norm-clique-small-m-2026-09-18/k5lane.sh
  - experiments/hermitian-edge-trace-norm-clique-small-m-2026-09-18/k5_partial_runs.log
distinct_from:
  hermitian-edge-trace-norm-clique-inequality: that is (UCI) for every m; this is the single case m = 5, its last open instance.
  hermitian-edge-trace-norm-clique-inequality-k4: that is m = 4 on the three-torus (done); this is m = 5 on the six-torus, with the same certificate scheme plus a symmetry reduction.
  hermitian-edge-trace-norm-clique-inequality-large-m: that proves m >= 6 by an energy LP, which provably cannot reach m = 5.
---

**ESTABLISHED (computer-assisted; certificates checked in exact rational arithmetic; unreviewed,
not Lean-verified; route `hermitian-edge-trace-norm-clique-inequality-k5-proof`).**
Every Hermitian `5 x 5` matrix `C` with `C_ii = 0` and `|C_ij| >= 1` for `i != j` satisfies

```text
|| C ||_1  >=  4 sqrt3  = 6.9282 .
```

The numerical minimum is `5 + sqrt5 = 7.236`. This was the last open case of the uniform clique
inequality. With it, `hermitian-edge-trace-norm-clique-inequality-by-size` proves (UCI) for every `m`.
Then Theorem 5(b) of `hermitian-edge-trace-norm-k4-free-h-perfect-proof` gives (**) for every
h-perfect graph, and in particular every perfect graph.

**Method.** This is the method of the `K_4` proof (`hermitian-edge-trace-norm-clique-inequality-k4-proof`,
Steps 1–4, which are written for general `m`), with `m = 5`, `T = 3.47` and `TARGET = 6.9282033`.
1. Gauge the star at vertex 1 to be real. This leaves six free phases.
2. Moduli above `T` are handled by `2 x 2` compression.
3. Otherwise a rational `Z`, checked exactly to satisfy `-I < Z < I`, gives the edge-separable bound
   `tr(ZC)`. Its exact minimum over a phase box closes the box.

*Symmetry reduction (proved).* Negation followed by conjugation with `diag(-1,1,1,1,1)` keeps the
star real and shifts every free phase by `pi`. Complex conjugation negates every free phase. So the
first free phase `theta_23` can be taken in `[0, pi/2]`. That interval is cut into 16 slices
`[i pi/32, (i+1) pi/32]`, `i = 0..15`, and in each slice the other five phases range over `[0, 2pi)^5`.

**Certified** (`k5_partial_runs.log`). All 16 slices `i = 0..15` print `ALL CLOSED`, and no box
failed. Lane w6-078 ran slices `0, 1, 2, 6, 7, 11, 12` and lane w7-078 ran the other nine. Each
slice took 28,538–31,852 closed boxes and 40,994–45,709 SDP solves, in 14 to 26 minutes on one core.
The smallest SDP value at any box centre was `7.2555` (slice 7), well above `6.928`.
