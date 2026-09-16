---
rg: 2
id: stw01-three-projection-via-corner-pair-additivity
kind: route
title: Settle the three-projection test by additivity of the two corner words r_1 r_2 r_1, r_1 r_3 r_1
target: stw01-three-projection-algebra-quasitraces-are-traces
requires:
  - stw01-three-projection-corner-pair-quasitrace-additivity
---

If every bounded 2-quasitrace on `P_3 = C^2 * C^2 * C^2` is additive on `h_2 = r_1 r_2 r_1`
and `h_3 = r_1 r_3 r_1`, then Problem I holds. In particular every bounded 2-quasitrace on
`P_3` is a trace. Full proof: Theorem 1 in
`research/artifacts/stw01-three-projection-corner-pair-test-2026-09-16.md`.

Outline.
1. **Step 0 (reviewed, unchanged).** If Problem I fails, the reviewed Step 0 of
   `research/artifacts/stw01-three-projection-universal-test-2026-09-12.md` applies. It uses
   Gow arXiv:2601.04431v2, Theorem A, Theorem 2.22 and Corollary 3.10, and gives a type `II_1`
   AW*-factor `M` with canonical quasitrace `tau`, and `x, y in M_+` with
   `D_tau(x, y) != 0`. Rescale so that `||x||, ||y|| <= 1`, which divides the defect by a
   positive constant.
2. **The 2-quasitrace on `M_2(M)`.** Blackadar–Handelman Corollary II.1.10, as quoted by Gow,
   gives `tau_4` on `M_4(M)`. Its restriction `tau~` to the upper-left `M_2(M)` is a bounded
   2-quasitrace with `tau~(z (+) 0) = tau(z)`.
3. **Corner dilation.** In `M_2(M)` put `P_1 = 1 (+) 0`, `P_2 = v_x v_x^*` with
   `v_x = (x^(1/2), (1 - x)^(1/2))^T`, and `P_3 = v_y v_y^*`. These are projections with
   `P_1 P_2 P_1 = x (+) 0` and `P_1 P_3 P_1 = y (+) 0`.
4. **Pull back.** The unital *-homomorphism `pi : P_3 -> M_2(M)`, `r_j -> P_j`, pulls `tau~` back
   to a bounded 2-quasitrace `sigma` on `P_3`, with
   `sigma(h_2 + h_3) - sigma(h_2) - sigma(h_3) = D_tau(x, y) != 0`. This contradicts the
   required claim.

So Problem I holds, and the target is its special case `A = P_3`. The external inputs are
exactly those of the reviewed route `stw01-problem-i-via-three-projection-algebra`, minus the
finite-spectrum density step.
