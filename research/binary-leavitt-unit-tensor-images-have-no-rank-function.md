---
rg: 2
id: binary-leavitt-unit-tensor-images-have-no-rank-function
kind: claim
title: The diagonal tensor square of the binary Leavitt unit group algebra admits no Sylvester rank function
distinct_from:
  odd-char-leavitt-unit-tensor-images-have-no-rank-function: that is the established odd-characteristic statement for degrees below the characteristic; this is the characteristic-two tensor square, where the scalar 2 used there vanishes.
  sylvester-rank-functions-on-leavitt-units-kill-two-root-defect: that says every rank function on the binary group algebra kills the two-root defect; this only concerns rank functions factoring through the diagonal tensor square, where the defect acts nonzero.
artifacts:
  - research/artifacts/diagonal-tensor-rank-functions-2026-09-12.md
---

**OPEN.**
- **Setup:** `R = L_(F_2)(1,2)`, `Γ = R^x`, and `B_2` is the image of `F_2[Γ] -> R ⊗ R`, `[g] -> g ⊗ g`.
- **Statement:** no ring that receives a unital ring homomorphism from `B_2` carries a Sylvester matrix rank
  function.

**What it bears on.**
- **The handle:** `[SG]` Section 3.4 (`research/artifacts/sylvester-rank-function-two-root-gate-2026-09-12.md`)
  names diagonal tensor powers as the only live construction handle for
  `binary-leavitt-units-carry-nonaugmentation-rank-function`. The two-root defect acts on `W ⊗ W` as
  `e_23 ⊗ e_12 + e_12 ⊗ e_23 != 0`.
- **If this claim holds:** the degree-two handle dies in characteristic two as well.
- **If it fails:** a rank function on `B_2` is a candidate detecting rank function. It must give
  `e_23 ⊗ e_12 + e_12 ⊗ e_23` positive rank.

## Attempts

- **2026-09-12, `w4-tensor-rankfn`: the odd-characteristic proof stops at the scalar `2`.**
  - **Where it fails:** in `B_2` the symmetrized roots `Sym_ij(a, b) = e_ij(a) ⊗ e_ij(b) + e_ij(b) ⊗ e_ij(a)`
    are still present (Step 1 of the artifact works in every characteristic). But the isometry pair gives
    `Sym_21(t_α, t_β) · Sym_12(s_α, s_β) = 2 e_22 ⊗ e_22 = 0`.
  - **What the other product gives:** `Sym_12(s_(00), s_(01)) · Sym_21(t_(00), t_(01))` has the form
    `P + Y` with `P` idempotent, `Y^2 = P` and `PY = YP = Y`, so `(P + Y)^2 = 0`.
  - **So:** products of opposite symmetrized roots give no idempotents. A replacement has to use the quadratic
    part `Q(a) = e(a) ⊗ e(a)` in `Δ_2(x(a)) - 1 = e(a) ⊗ 1 + 1 ⊗ e(a) + Q(a)`. `Q` is additive only modulo
    symmetrized roots, `Q(a + b) = Q(a) + Q(b) + Sym(e(a), e(b))`, and it is untested.
