---
rg: 2
id: paradoxical-steinberg-elementary-simple-kazhdan-not-mf-proof
kind: route
title: Proof — the reviewed simplicity theorem for the group side, and the rank-two full-defect theorem for MF quotients
target: paradoxical-steinberg-elementary-simple-kazhdan-not-mf
requires:
  - steinberg-elementary-groups-are-simple-mod-centre
  - full-defect-ring-non-mf-at-rank-two
artifacts:
  - research/artifacts/un-boundary-families-2026-09-13-part2.md
---

1. **Simplicity and (T).** `steinberg-elementary-groups-are-simple-mod-centre` applies to `A = A_(F_q)(𝒢)`, since
   `𝒢` is Hausdorff ample, effective and minimal, and its unit space is compact and infinite.
   - Normal subgroups of `EL_N(A)` are central or everything, and `Z ⊆ F_q^× I_N`.
   - Because `F_q` is finite and `A` is finitely generated, the quotient is an infinite finitely generated simple
     group with (T).
2. **No MF quotient.** `ts = 1` and `A(1 - st)A = A` are exactly the hypotheses of
   `full-defect-ring-non-mf-at-rank-two`, so every homomorphism from `EL_n(A)`, `n >= 2`, to an MF group is trivial.
   Composing with the quotient map gives the same for `EL_N(A)/Z`.
3. **A Leavitt copy gives the defect.** With Leavitt generators satisfying `t_i s_j = δ_ij` and `Σ_i s_i t_i = 1`,
   take `s = s_1` and `t = t_1`. Then `1 - s_1 t_1 = Σ_(i>=2) s_i t_i` and `t_2 (1 - s_1 t_1) s_2 = 1`, as in the
   printed Cor l.1016.
