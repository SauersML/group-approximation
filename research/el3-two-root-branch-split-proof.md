---
rg: 2
id: el3-two-root-branch-split-proof
kind: route
title: Expand the commutator, split x_ab(1) over the Leavitt idempotents, and conjugate by the branch swap
target: el3-two-root-violation-splits-over-leavitt-branches
requires:
  - leavitt-gl-equals-el-and-perfect-unit-group
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/el3-two-root-self-similarity-2026-09-12.md
---

Artifact Sections 2–3.

- **Defect factorization.** `x_ik(ab) = (1+X)(1+Y)(1+X)(1+Y)` in characteristic two, and
  `(1+X)(YX)(1+Y) = YX + XYX + YXY + XYXY` accounts for every term except `XY`.
- **Commutation and the split.** `x_ab(1) = x_ab(e_0) x_ab(e_1)`, and
  `[x_12(e_i), x_23(e_(1-i))] = x_13(0) = 1`. Expanding the nine products and grouping gives the
  formula.
- **The swap.** `w^2 = 1`, `w s_0 = s_1` and `t_0 w = t_1`, so `diag(w,w,w)` conjugates `x_ab(e_0)`
  to `x_ab(e_1)` and fixes `x_ab(1)`. It lies in `EL_3(R)` because `GL_3(R) = EL_3(R)`
  (the prerequisite).
- **The bound.** `iota_0` is an injective endomorphism (`t_0 s_0 = 1`) with
  `iota_0(x_ab(1)) = x_ab(e_0)`, and rank is subadditive.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 43 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
