import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# (V2) The one-operator estimate: approximate eigenvectors without spectral projections

Glimm's lemma produces its vectors from a self-adjoint `b` and a point `μ` of
its essential spectrum: one wants a unit `ξ`, orthogonal to a prescribed
finite-dimensional subspace, with `‖(b - μ) ξ‖` small.  The textbook route
takes the spectral projection of a small interval about `μ`, and that route is
closed here — the pinned Mathlib has the *continuous* functional calculus and no
Borel one, no spectral measures.

The pin-native substitute is to cut with a continuous bump instead of a
projection.  If `f` vanishes off the `δ`-interval about `μ` then
`|t - μ|² f(t)² ≤ δ² f(t)²` pointwise on the spectrum, and the calculus is
order-preserving, so the same inequality holds between the operators — whence
`‖(b - μ) f(b)η‖ ≤ δ ‖f(b)η‖` for *every* `η`, with no control on `η` needed.
Vectors in the range of `f(b)` are therefore approximate eigenvectors, and the
orthogonality to a finite-dimensional subspace is arranged separately, by a
dimension count against the range.

## What makes this cheap here

Two facts about `B(H)`, both registered instances at the pin, and both the
opposite of the situation in the doubled-model zone where this tree usually has
to supply `CStarAlgebra.spectralOrder` by hand:
`ContinuousLinearMap.instLoewnerPartialOrder` puts the Loewner order on
`H →L[ℂ] H`, and `ContinuousLinearMap.instStarOrderedRing` makes it a
`StarOrderedRing`, so `cfc_mono` applies with no local instance juggling.  And
the Loewner order is *definitionally* positivity of the difference
(`le_def` is `Iff.rfl`), which is what lets the bridge below read a vector
inequality off an operator inequality in one step.

The first lemma is stated for operators alone, with no functional calculus in
it: `‖S η‖ ≤ ‖T η‖` whenever `S⋆S ≤ T⋆T`.  That is the whole of the passage
from the order to the vectors, it is what (V3) will want again when it compares
compressions, and it is worth having once.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## From the operator order to the vectors -/

/-- **The bridge.**  `S⋆S ≤ T⋆T` bounds `S` by `T` pointwise on vectors.  Both
sides are quadratic forms of the Loewner order, and that order is positivity of
the difference by definition. -/
theorem norm_apply_le_of_star_mul_self_le {S T : H →L[ℂ] H}
    (h : star S * S ≤ star T * T) (η : H) : ‖S η‖ ≤ ‖T η‖ := by
  have key : ∀ R : H →L[ℂ] H,
      RCLike.re ⟪η, (star R * R) η⟫_ℂ = ‖R η‖ ^ 2 := by
    intro R
    have h1 : ⟪η, (star R * R) η⟫_ℂ = ⟪R η, R η⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact ContinuousLinearMap.adjoint_inner_right R η (R η)
    rw [h1]
    exact inner_self_eq_norm_sq (R η)
  have hpos : (star T * T - star S * S).IsPositive := h
  have hform : 0 ≤ RCLike.re ⟪η, (star T * T - star S * S) η⟫_ℂ :=
    hpos.re_inner_nonneg_right η
  have hsplit : ⟪η, (star T * T - star S * S) η⟫_ℂ
      = ⟪η, (star T * T) η⟫_ℂ - ⟪η, (star S * S) η⟫_ℂ := by
    rw [sub_apply, inner_sub_right]
  rw [hsplit, map_sub, key T, key S] at hform
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  linarith

/-! ## The comparison of two continuous cuts -/

/-- **Comparison.**  If `g² ≤ f²` on the spectrum then `g(b)` is bounded by
`f(b)` on every vector.  The star drops out because both functions are real,
and the squares are `cfc`s of the pointwise squares. -/
theorem norm_cfc_apply_le_of_sq_le (b : H →L[ℂ] H) (_hb : IsSelfAdjoint b)
    (f g : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ b))
    (hg : ContinuousOn g (spectrum ℝ b))
    (hle : ∀ t ∈ spectrum ℝ b, g t ^ 2 ≤ f t ^ 2) (η : H) :
    ‖cfc g b η‖ ≤ ‖cfc f b η‖ := by
  have hstar : ∀ h : ℝ → ℝ, star (cfc h b) = cfc h b := by
    intro h
    rw [← cfc_star]
    exact cfc_congr fun t _ ↦ star_trivial (h t)
  have hsq : ∀ h : ℝ → ℝ, ContinuousOn h (spectrum ℝ b) →
      star (cfc h b) * cfc h b = cfc (fun t ↦ h t ^ 2) b := by
    intro h hcont
    rw [hstar h, ← cfc_mul h h b hcont hcont]
    exact cfc_congr fun t _ ↦ (pow_two (h t)).symm
  refine norm_apply_le_of_star_mul_self_le ?_ η
  rw [hsq g hg, hsq f hf]
  exact cfc_mono hle

/-! ## The approximate eigenvector estimate -/

/-- **The estimate Glimm's lemma spends.**  A continuous cut `f` whose square is
crushed by `δ²` away from `μ` — which a bump supported in the `δ`-interval
satisfies for free — makes every vector in the range of `f(b)` an approximate
eigenvector of `b` at `μ`, with relative error `δ`.

No spectral projection appears, and no hypothesis is placed on `η`: the
inequality is between the two operators, so it holds at every vector at once. -/
theorem norm_sub_algebraMap_apply_le (b : H →L[ℂ] H) (hb : IsSelfAdjoint b)
    (μ δ : ℝ) (hδ : 0 ≤ δ) (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ b))
    (hsupp : ∀ t ∈ spectrum ℝ b, ((t - μ) * f t) ^ 2 ≤ (δ * f t) ^ 2) (η : H) :
    ‖(b - algebraMap ℝ (H →L[ℂ] H) μ) (cfc f b η)‖ ≤ δ * ‖cfc f b η‖ := by
  have hcontd : ContinuousOn (fun t : ℝ ↦ t - μ) (spectrum ℝ b) :=
    continuousOn_id.sub continuousOn_const
  have hcont1 : ContinuousOn (fun t : ℝ ↦ (t - μ) * f t) (spectrum ℝ b) :=
    hcontd.mul hf
  have hcont2 : ContinuousOn (fun t : ℝ ↦ δ * f t) (spectrum ℝ b) :=
    continuousOn_const.mul hf
  have hcomp := norm_cfc_apply_le_of_sq_le b hb (fun t ↦ δ * f t)
    (fun t ↦ (t - μ) * f t) hcont2 hcont1 hsupp η
  have hL : cfc (fun t ↦ (t - μ) * f t) b
      = (b - algebraMap ℝ (H →L[ℂ] H) μ) * cfc f b := by
    rw [cfc_mul _ _ b hcontd hf]
    congr 1
    rw [cfc_sub (fun t : ℝ ↦ t) (fun _ : ℝ ↦ μ) b continuousOn_id continuousOn_const,
      cfc_id' ℝ b, cfc_const μ b]
  have hR : cfc (fun t ↦ δ * f t) b = δ • cfc f b := cfc_const_mul δ f b
  rw [hL, hR] at hcomp
  refine le_trans (le_of_eq ?_) (le_trans hcomp (le_of_eq ?_))
  · rfl
  · rw [smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ]

end

end ShulmanFill
end GroupApproximation
