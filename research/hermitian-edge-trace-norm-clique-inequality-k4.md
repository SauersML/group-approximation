---
rg: 2
id: hermitian-edge-trace-norm-clique-inequality-k4
kind: claim
title: The clique inequality holds on K4 - a Hermitian 4x4 matrix with zero diagonal and off-diagonal moduli at least 1 has trace norm at least 3 sqrt3
artifacts:
  - research/hermitian-edge-trace-norm-clique-inequality-k4-proof.md
  - experiments/hermitian-edge-trace-norm-clique-small-m-2026-09-18/cliquebb.py
  - experiments/hermitian-edge-trace-norm-clique-small-m-2026-09-18/k4_full_torus.log
distinct_from:
  hermitian-edge-trace-norm-clique-inequality: that is (UCI) for every m; this is the single case m = 4, which was its smallest open instance.
  hermitian-edge-trace-norm-clique-inequality-large-m: that proves m >= 6 by an energy LP, which provably cannot reach m = 4; this proves m = 4 by a different, computer-assisted method.
---

**ESTABLISHED (computer-assisted; certificates checked in exact rational arithmetic; unreviewed,
not Lean-verified; route `hermitian-edge-trace-norm-clique-inequality-k4-proof`).**

**Theorem.** Every Hermitian `4 x 4` matrix `C` with `C_ii = 0` and `|C_ij| >= 1` for `i != j`
satisfies

```text
|| C ||_1  >=  3 sqrt3 .
```

So the Hermitian edge inequality (**) holds on `K_4` with unit weights. With
`hermitian-edge-trace-norm-clique-inequality-large-m` (`m >= 6`) and the known `m <= 3`, the clique
inequality (UCI) is now open only at `m = 5`. The numerical minimum is `2 + 2 sqrt3 = 5.464`.

**Proof idea.**
1. Gauge the star at vertex 1 to be real. This leaves three free phases (the flux torus `T^3`) and
   moduli `t_ij >= 1`.
2. If some `t_ij > 2.6`, a `2 x 2` compression already gives `||C||_1 > 5.2`.
3. Otherwise, any `Z` with `||Z||_op <= 1` gives `||C||_1 >= tr(ZC) = sum_{i<j} t_ij 2Re(Z_ji e^{i theta_ij})`.
   This is separable in the edges, so its minimum over a box of phases and over `t in [1, 2.6]` is
   computed exactly.
4. SDP duals at the box centres, rounded to rationals and checked exactly, cover `T^3` with 584 boxes.

The method works for any fixed `m`. `m = 5` needs the six-dimensional torus.
