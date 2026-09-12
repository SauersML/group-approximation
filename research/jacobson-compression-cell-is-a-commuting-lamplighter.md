---
rg: 2
id: jacobson-compression-cell-is-a-commuting-lamplighter
kind: claim
title: The commuting element of the Jacobson compression cell lies in a finite simple commutant cell with pairwise commuting compressor conjugates
distinct_from:
  binary-jacobson-finitary-whitehead-shift-is-marked-lef: that periodizes the whole finitary kernel under the balanced Whitehead shift and proves LEF; this identifies the commuting element of the rank-four compression cell as part of a GL_3(F_2) in the commutant of the Kazhdan subgroup, and describes its compressor conjugates.
artifacts:
  - research/artifacts/jacobson-rank-radical-support-bound-and-symbol-firewall-2026-09-12.md
---

**ESTABLISHED** by `jacobson-compression-cell-is-a-commuting-lamplighter-proof`.

Let `J = F_2<S,T | TS = 1>`, `Q = 1 - ST`, `e_ab = S^a Q T^b`, `E_4 = EL_4(J)`, and `H = EL_3(J)` on
coordinates `1, 2, 3`. Take the compression cell of `non_mf_groups_exist.tex`
(`lem:ring-compression-cell`):
* `u x_ij(a) u^(-1) = x_ij(SaT)` for `1 <= i != j <= 3`;
* `c = diag(1, 1, 1, 1 + QT)` in `C_(E_4)(H)`;
* `u c u^(-1) = x_12(Q)`, and `[x_12(Q), x_23(1)] = x_13(Q)`.

Put `K_1 = <x_ij(Q) : 1 <= i != j <= 3>` and `K_j = u^(j-1) K_1 u^(1-j)` for `j in Z`. Then:

1. `K_1 = GL_3(F_2) <= H`, and `K_1` commutes with `u H u^(-1)`.
2. `K_0 = u^(-1) K_1 u` lies in `C_(E_4)(H)`, and `c in K_0`.
3. The `K_j` pairwise commute and lie in the finitary kernel.
   * For `j >= 1`, `K_j = <x_ik(e_(j-1,j-1))> <= H`.
   * For `j <= 0`, `K_j <= C_(E_4)(H)`.
4. The constants `EL_3(F_2)` centralize `K_j` for `j <= 0`, and act on `K_j` for `j >= 1` through
   index `j - 1`. Also `u^(-1) x_23(1) u = w_0 x_23(1)`, where `w_0 = u^(-1) x_23(Q) u` lies in `K_0`.

**Consequence for models.** In every homomorphism `sigma` into a group, `sigma(K_0)` commutes with
`sigma(H)`, and `sigma(K_0) != 1` iff the head `x_13(Q)` survives. The operator-norm theorem
`binary-jacobson-steinberg-head-root-is-mf-invisible` transports the commutation along `u` and
makes the simple group `sigma(K_1)` central in `sigma(H)`, hence trivial. In a rank model the missing
step is exactly that transport for this one finite simple cell. No rounding of `sigma(K_0)` is
needed (artifact Proposition 1(3), Section 2).
