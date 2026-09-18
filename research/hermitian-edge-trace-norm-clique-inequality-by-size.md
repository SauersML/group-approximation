---
rg: 2
id: hermitian-edge-trace-norm-clique-inequality-by-size
kind: route
title: The uniform clique inequality for every m, by cases - elementary for m <= 3, flux-torus branch-and-bound for m = 4 and m = 5, the energy LP for m >= 6
target: hermitian-edge-trace-norm-clique-inequality
requires:
  - hermitian-edge-trace-norm-k4-free-h-perfect
  - hermitian-edge-trace-norm-clique-inequality-k4
  - hermitian-edge-trace-norm-clique-inequality-k5
  - hermitian-edge-trace-norm-clique-inequality-large-m
artifacts:
  - research/hermitian-edge-trace-norm-clique-inequality-k4-proof.md
  - research/hermitian-edge-trace-norm-clique-inequality-large-m-proof.md
---

This proof assembles cases; it is unreviewed and not Lean-verified. Lane w6-078, 2026-09-18.

**Theorem (UCI).** For every `m >= 2` and every Hermitian `m x m` matrix `C` with `C_ii = 0` and
`|C_ij| >= 1` for `i != j`, `||C||_1 >= sqrt3 (m - 1)`.

**Proof.** We split by `m`.
- **`m = 2`.** The eigenvalues are `+-|C_12|`, so `||C||_1 = 2|C_12| >= 2 > sqrt3`.
- **`m = 3`.** Since `tr C = 0`, the positive eigenvalues and the moduli of the negative ones have
  the same sum `s`, so `||C||_1 = 2s`. Also
  `||C||_F^2 = sum lambda^2 <= (sum_{lambda>0} lambda)^2 + (sum_{lambda<0} |lambda|)^2 = 2 s^2`.
  Hence `||C||_1 >= sqrt2 ||C||_F`. Since `||C||_F^2 = 2 sum_{i<j} |C_ij|^2 >= 6`, this gives
  `||C||_1 >= 2 sqrt3`. This is Theorem 5(a) of `hermitian-edge-trace-norm-k4-free-h-perfect-proof`.
- **`m = 4`.** This is `hermitian-edge-trace-norm-clique-inequality-k4` (computer-assisted, exact
  rational certificates).
- **`m = 5`.** This is `hermitian-edge-trace-norm-clique-inequality-k5` (computer-assisted, exact
  rational certificates; still partly outstanding, see below).
- **`m >= 6`.** This is `hermitian-edge-trace-norm-clique-inequality-large-m`: a rank-one reduction,
  averaging, and an interval-checked Yudin-type LP certificate.

These cases cover every `m >= 2`. ∎

**Status of the pieces.** Every piece is ESTABLISHED except `m = 5`. The node
`hermitian-edge-trace-norm-clique-inequality-k5` is certified on part of its symmetry-reduced domain,
and the rest is a mechanical computation with the landed scripts. So this route is complete once that
node is.

**Consequence.** By Theorem 5(b) of `hermitian-edge-trace-norm-k4-free-h-perfect-proof`, (**) then
holds for every h-perfect graph, including every perfect graph.
