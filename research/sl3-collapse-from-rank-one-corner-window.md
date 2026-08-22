---
rg: 2
id: sl3-collapse-from-rank-one-corner-window
kind: route
title: The SL_2 corner window reduces the SL_3 carrier collapse to the rank-one vanishing branch
target: hnn-carrier-factorial-character-collapse
requires: [sl2-carrier-vanishing-branch-character-collapse]
artifacts:
  - research/artifacts/noncommutative-solenoid-unique-trace-memo-2026-08-22.md
---

Let `tau` be a factorial hyperlinear character of the n = 3 carrier `H`
with `tau|_Gamma = delta_e`.  Steps, each unconditional:

1. **Corner window.**  `Delta =` upper-left `SL_2(Z[1/p])` corner;
   `E := <Delta, t>_H ~= <SL_2(Z[1/p]), s | [s, SL_2(Z)] = 1>` by Britton
   (non-integral corner entries leave `Lambda`).  `rho := tau|_E` is a
   hyperlinear trace (GNS is a subalgebra of the embedded `M_tau`) with
   `rho|_Delta = delta_e`.
2. **Components.**  Ergodic decomposition `rho = int sigma_x`: a.e.
   `sigma_x` is factorial and HYPERLINEAR — corners of matrix ultraproducts
   are matrix ultraproducts, martingale convergence identifies `sigma_x` as
   a weak-* limit of corner traces, and hyperlinear traces are weak-*
   closed.
3. **Corner classification.**  Peterson-Thom (arXiv:1303.4007 = Crelle 716
   (2016) 207-228, Thm 2.6): extremal characters of `SL_2(Z[1/p])` (a
   localization with infinitely many units) factor through finite quotients
   or vanish off `{±I}`.  Pick `g_j != ±I` in the intersection of all
   normals of index <= j; every finite-quotient extremal is eventually 1 on
   `g_j`, every vanishing-branch extremal is 0 there, so
   `lim_j sigma_x(g_j) =` the finite-quotient mass `f_x`, and
   `int f_x = lim_j rho(g_j) = lim_j delta_e(g_j) = 0`: a.e. component is
   vanishing-branch on the corner.  (No CSP is used; index-bounded cores
   suffice.)
4. **Consume the hole and regenerate.**  The target's input
   `sl2-carrier-vanishing-branch-character-collapse` applies to a.e.
   `sigma_x`, giving letter-centrality against `Delta`; integrate, use
   Cauchy-Schwarz equality against the separating trace vector, and
   `Gamma = <Lambda, Delta>` (signed Weyl conjugates of the corner roots
   give all root groups; elementary generation over the Euclidean `Z[1/p]`)
   to get `[pi_tau(t), pi_tau(Gamma)] = 0`, i.e. (FC1).

Full proofs of the lemmas (weak-* closedness, component hyperlinearity,
congruence-escape averaging): THE MEMO, Section B.5.  Value: with the
established `rcc-carrier-character-face-compression`, this route makes the
whole SL_3 lane rest on ONE rank-one character claim — an independent
subgroup-theoretic confirmation of the CORE A capstone, and the first
strict ordering between the n = 2 and n >= 3 carrier collapse claims.
