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
- **2026-09-12, `w4-tensor-rankfn`: survivors localized** (`binary-tensor-square-rank-functions-live-on-diagonal-norms`,
  artifact Section 2).
  - **Off-diagonal norms are null:** `Sym(p_X, p_Y)` has rank `0` for disjoint clopens. Here the isometry
    argument works with no factor `2`, because the slots carry different sets.
  - **Localization:** `rk z = rk(Q_P z Q_P)` for every clopen partition with at least 3 pieces.
  - **Tate–Frobenius:** `B_2/(B_2 ∩ N) ≅ R`, so a rank function must be positive on some diagonal-block norm
    `Sym(p_i a p_j, p_i b p_j)`.
  - **Next test:** whether diagonal-block norms of distinct parallel partial isometries can be nulled at
    finer scales. `Sym(u, u) = 0` in characteristic two.
- **2026-09-12, `w4-tensor-rankfn`: the target-relevant half is settled**
  (`binary-tensor-square-rank-functions-kill-two-root-defect`, artifact Theorem 2.4).
  - **The defect dies:** `Δ_2(D)` has off-diagonal left support `Sym(p_[10], p_[0])`, which is null. So every
    rank function through `B_2` pulls back to the augmentation rank, and the tensor-square handle cannot give
    a detecting function.
  - **What stays open here:** whether `B_2` carries any rank function at all. It does iff `ker Δ_2 ⊆ ker ε`,
    and then it is `x -> [ε(x) != 0]`. This no longer bears on the averaging targets.
  - **Degree `n >= 3` over `F_2`:** open. Supports with a repeated set bring back the scalar `2`.
