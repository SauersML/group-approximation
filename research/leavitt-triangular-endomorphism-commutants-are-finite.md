---
rg: 2
id: leavitt-triangular-endomorphism-commutants-are-finite
kind: claim
title: Unital endomorphisms of L_K(1,2) given by core or triangular units have finite-dimensional relative commutants, so a unital map from the tensor square cannot use such units
distinct_from:
  leavitt-triangular-units-have-linear-depth-growth: that is depth growth of triangular units themselves; this bounds the relative commutant of the endomorphism a triangular unit defines.
  leavitt-endomorphism-relative-commutants-are-finite: that is the open statement for every unit; this proves it for units in H_<= or H_>=.
artifacts:
  - research/artifacts/leavitt-relative-commutants-2026-09-13.md
---

**ESTABLISHED** by `leavitt-triangular-endomorphism-commutants-are-finite-proof` (unreviewed).

Let `K` be any field, `R = L_K(1,2)`, `R = ⊕ R_d` its `Z`-grading, and `phi(x) = s_0 x t_0 + s_1 x t_1`. Every
unital endomorphism is `rho_u(s_i) = u s_i`, `rho_u(t_i) = t_i u^(-1)` for a unit `u`. Its relative commutant is
`C_u = C_R(rho_u(R)) = { z : z = u phi(z) u^(-1) }`.

1. **Core units.** If `u` is a unit in `M_(2^k)(K) = span{ s_α t_β : |α| = |β| = k }`, then `C_u` is graded, and
   `C_u ∩ R_d` is `0` unless `|d| <= 2k - 2`. For `d >= 0` it lies in `span{ s_α t_β : |β| = k - 1 }`, and for
   `d < 0` in `span{ s_α t_β : |α| = k - 1 }`. So `dim C_u <= Σ_(|d| <= 2k-2) 2^(2k-2+|d|)`.
2. **Triangular units.** If `u, u^(-1) ∈ R_(<=0)`, or `u, u^(-1) ∈ R_(>=0)`, then `dim C_u <= dim C_(u_0)` is
   finite, where `u_0` is the degree-zero component.
3. **Question 5.7.** Let `f : L ⊗ L -> L` be unital, and `u = Σ_i f(s_i ⊗ 1) t_i`. Then for every unit `w`, the
   twisted conjugate `w u phi(w)^(-1)` is not triangular. The same holds for `v = Σ_i f(1 ⊗ s_i) t_i`.

So a unital embedding `L_2 ⊗ L_2 -> L_2` (Ara--Cortiñas, arXiv:1108.0352v3, Question 5.7), if one exists,
cannot use any localized endomorphism, nor any unit built from nilpotents of one sign together with core units.

**Evidence.** 32 random units of `GL_4(F_2)` and `GL_8(F_2)`, and 843 random short words, all have
relative commutants of dimension `<= 2` in `R_N` for `N <= 3` or `4`. The flip unit gives `M_2(F_2)`. See
`research/artifacts/leavitt-relative-commutants-2026-09-13.md`, Section 4.
