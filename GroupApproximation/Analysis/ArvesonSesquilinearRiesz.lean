import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# A bounded sesquilinear form is the matrix of an operator

`Analysis/ArvesonBHTarget` reduces Arveson's extension theorem at a `B(H)`
target to one limit step, and that step produces its operator from matrix
coefficients: a weak limit of maps `A → B(H)` is a form first and an operator
only afterwards.  This module is the passage from the one to the other, kept
apart from the limit because it is a fact about Hilbert spaces and mentions
neither `A` nor the approximants.

Mathlib has the substance, in `InnerProductSpace.continuousLinearMapOfBilin`
(`Mathlib/Analysis/InnerProductSpace/Dual.lean`): a *bundled* sesquilinear map
`H →L⋆[ℂ] H →L[ℂ] ℂ` is represented by an operator.  What it does not do is
bundle a bare two-variable function, and that is what a limit hands you.  So the
work here is the two layers of `LinearMap.mkContinuous`, and the one thing worth
saying out loud is the orientation.

`continuousLinearMapOfBilin_apply` reads `⟪B♯ v, w⟫ = B v w`, so `B` is
conjugate-linear in its *first* slot; the form a limit of matrix coefficients
produces is `L v w = lim ⟪v, Ψₙ x w⟫`, conjugate-linear in `v`, which is the
slot that ends up *second*.  The object to feed in is therefore
`B w v = conj (L v w)` — conjugate-linear in `w` because `L` is linear in it,
linear in `v` because `L` is conjugate-linear in it — and the operator is
`B♯`, with the two conjugations cancelling at the end.  Getting this backwards
type-checks nowhere near the error, so it is stated here once and consumed as a
black box.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **The inner layer.**  At a fixed second argument, a form that is additive
and conjugate-homogeneous in the first and bounded there is, after conjugation,
a continuous linear functional of norm at most `C ‖w‖. -/
theorem exists_functional_of_sesq (L : H → H → ℂ) (C : ℝ) (hC : 0 ≤ C) (w : H)
    (hadd : ∀ v v' : H, L (v + v') w = L v w + L v' w)
    (hsmul : ∀ (z : ℂ) (v : H), L (z • v) w = (starRingEnd ℂ) z * L v w)
    (hnorm : ∀ v : H, ‖L v w‖ ≤ C * ‖v‖ * ‖w‖) :
    ∃ f : H →L[ℂ] ℂ, (∀ v : H, f v = (starRingEnd ℂ) (L v w)) ∧ ‖f‖ ≤ C * ‖w‖ := by
  have hbound : ∀ v : H, ‖(starRingEnd ℂ) (L v w)‖ ≤ C * ‖w‖ * ‖v‖ := by
    intro v
    rw [RCLike.norm_conj]
    calc ‖L v w‖ ≤ C * ‖v‖ * ‖w‖ := hnorm v
      _ = C * ‖w‖ * ‖v‖ := by ring
  refine ⟨LinearMap.mkContinuous
    { toFun := fun v ↦ (starRingEnd ℂ) (L v w)
      map_add' := fun v v' ↦ by
        show (starRingEnd ℂ) (L (v + v') w)
          = (starRingEnd ℂ) (L v w) + (starRingEnd ℂ) (L v' w)
        rw [hadd, map_add]
      map_smul' := fun z v ↦ by
        show (starRingEnd ℂ) (L (z • v) w)
          = (RingHom.id ℂ) z • (starRingEnd ℂ) (L v w)
        rw [hsmul, map_mul, starRingEnd_self_apply, RingHom.id_apply, smul_eq_mul] }
      (C * ‖w‖) hbound, fun v ↦ ?_,
    LinearMap.mkContinuous_norm_le _ (mul_nonneg hC (norm_nonneg w)) hbound⟩
  simp only [LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]

/-- **A bounded sesquilinear form is the matrix of an operator.**  Conjugate
linear in the first variable, linear in the second, bounded by `C ‖v‖ ‖w‖`: then
there is one `T` with `⟪v, T w⟫ = L v w` throughout.

The form is given as a bare function, which is how a weak limit produces it; the
bundling is the content. -/
theorem exists_continuousLinearMap_of_sesq (L : H → H → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hadd_left : ∀ v v' w : H, L (v + v') w = L v w + L v' w)
    (hsmul_left : ∀ (z : ℂ) (v w : H), L (z • v) w = (starRingEnd ℂ) z * L v w)
    (hadd_right : ∀ v w w' : H, L v (w + w') = L v w + L v w')
    (hsmul_right : ∀ (z : ℂ) (v w : H), L v (z • w) = z * L v w)
    (hnorm : ∀ v w : H, ‖L v w‖ ≤ C * ‖v‖ * ‖w‖) :
    ∃ T : H →L[ℂ] H, ∀ v w : H, ⟪v, T w⟫_ℂ = L v w := by
  choose g hgapply hgnorm using fun w ↦
    exists_functional_of_sesq L C hC w (fun v v' ↦ hadd_left v v' w)
      (fun z v ↦ hsmul_left z v w) (fun v ↦ hnorm v w)
  have hBadd : ∀ w w' : H, g (w + w') = g w + g w' := by
    intro w w'
    refine ContinuousLinearMap.ext fun v ↦ ?_
    simp only [add_apply, hgapply]
    rw [hadd_right, map_add]
  have hBsmul : ∀ (z : ℂ) (w : H), g (z • w) = (starRingEnd ℂ) z • g w := by
    intro z w
    refine ContinuousLinearMap.ext fun v ↦ ?_
    simp only [smul_apply, hgapply, smul_eq_mul]
    rw [hsmul_right, map_mul]
  obtain ⟨B, hBapply⟩ : ∃ B : H →SL[starRingEnd ℂ] (H →L[ℂ] ℂ),
      ∀ w v : H, B w v = (starRingEnd ℂ) (L v w) := by
    refine ⟨LinearMap.mkContinuous
      { toFun := g, map_add' := hBadd, map_smul' := hBsmul } C hgnorm, fun w v ↦ ?_⟩
    simp only [LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
    exact hgapply w v
  refine ⟨InnerProductSpace.continuousLinearMapOfBilin B, fun v w ↦ ?_⟩
  rw [← inner_conj_symm v (InnerProductSpace.continuousLinearMapOfBilin B w),
    InnerProductSpace.continuousLinearMapOfBilin_apply, hBapply, starRingEnd_self_apply]

end

end CStarExactness
end GroupApproximation
