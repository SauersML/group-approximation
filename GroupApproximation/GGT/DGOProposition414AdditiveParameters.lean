import GroupApproximation.GGT.DGOProposition414LinearSumBound
import GroupApproximation.GGT.CayleyFourPointConverse

/-!
# The proved DGO sum bound at every real additive constant

Rounding the additive error upwards weakens the side inequalities. This
monotonicity supplies a real-parameter bound from the natural-parameter
surgery theorem and converts the original Cayley hyperbolicity hypothesis
to the four-point form used by that theorem.
-/

namespace GroupApproximation.GGT.OsinComponents

open GroupApproximation.GGT.DGOPolygonCut

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- A uniform bound for a larger additive error covers smaller errors too. -/
theorem DGOUniformSumBound.of_error_le
    {D : RelGenSet G Lambda} {mu c₀ c₁ : ℝ} {C : ℕ}
    (hbound : DGOUniformSumBound D mu c₁ C) (hc : c₀ ≤ c₁) :
    DGOUniformSumBound D mu c₀ C := by
  intro n v word cut I lam hlet hclosed hcut hI hedge hcomp hiso hquasi
  apply hbound n v word cut I lam hlet hclosed hcut hI hedge hcomp hiso
  intro s hs hnot p q hp hpq hq
  have h := hquasi s hs hnot p q hp hpq hq
  linarith

end GroupApproximation.GGT.OsinComponents

namespace GroupApproximation.GGT.DGOProposition414

open GroupApproximation.GGT.OsinComponents
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- The proved sum bound allows any real additive constant. -/
theorem exists_uniformSumBound_one_real
    (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {δ : ℕ} (c : ℝ) (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∃ C : ℕ, 0 < C ∧ DGOUniformSumBound D 1 c C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniformSumBound_one D hsymm ⌈c⌉₊ hδ
  exact ⟨C, hC, hbound.of_error_le (Nat.le_ceil c)⟩

/-- The multiplicative-constant-one sum bound under the original Cayley
hyperbolicity and base-symmetry hypotheses. -/
theorem exists_uniformSumBound_one_of_hyperbolic
    (D : RelGenSet G Lambda)
    (hhyp : ∃ delta : ℝ, IsHyperbolicSpace delta (Cayley D.alphabet))
    (hbase : DGO421BaseSymmetric D) (c : ℝ) :
    ∃ C : ℕ, 0 < C ∧ DGOUniformSumBound D 1 c C := by
  obtain ⟨delta, hdelta⟩ := hhyp
  exact exists_uniformSumBound_one_real D hbase c
    (isFourPointHyperbolic_of_isHyperbolicSpace_cayley D.alphabet hdelta)

end GroupApproximation.GGT.DGOProposition414

#audit_axioms GroupApproximation.GGT.OsinComponents.DGOUniformSumBound.of_error_le
#audit_axioms GroupApproximation.GGT.DGOProposition414.exists_uniformSumBound_one_real
#audit_axioms GroupApproximation.GGT.DGOProposition414.exists_uniformSumBound_one_of_hyperbolic
