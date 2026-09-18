import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.ChoiEffrosUcpPositive
import GroupApproximation.Analysis.QuasidiagonalTrace
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-28c, part 2: Kadison--Schwarz and the Schwarz-defect comparison

* **Kadison--Schwarz for a ucp `ρ : A → M_Y`.**  `ρ(a a⋆) − ρ(a) ρ(a)⋆` is PSD.  Apply complete
  positivity to the pair `(a⋆, 1)` with the vector pair `(v, −ρ(a)⋆ v)`.
* **Defect comparison.**  Let `G` satisfy `⟨G, G⟩ = 1`, and let `x = ρ a`.  Then
  `0 ≤ ψ_G(x x⋆) − ψ_G(x) ψ_G(x)⋆ ≤ ψ_G(ρ(a a⋆)) − ψ_G(x) ψ_G(x)⋆`.  The lower bound comes from
  the column Hilbert module.  The upper bound is Kadison--Schwarz for `ρ` pushed through the
  positive map `ψ_G`.  So the first norm is at most the second.
* **An elementary norm bound**, which converts approximation on `F ∪ F F⋆` into a Schwarz-defect
  bound.
-/

set_option linter.unusedSimpArgs false

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open Matrix Quasidiagonal
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

/-- The quadruple sum in `IsCompletelyPositiveOnMatrices` is a sesquilinear form. -/
theorem choiEffrosUcp_form_eq {Y : Type} [Fintype Y] (u : Y → ℂ) (N : Matrix Y Y ℂ)
    (w : Y → ℂ) :
    ∑ x, ∑ y, (starRingEnd ℂ) (u x) * N x y * w y = star u ⬝ᵥ (N *ᵥ w) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply,
    mul_assoc]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffrosUcp_form_eq

/-- **Kadison--Schwarz** for a unital completely positive `ρ : A → M_Y`. -/
theorem choiEffrosUcp_kadisonSchwarz {Y : FiniteModel} (ρ : A →ₗ[ℂ] Matrix Y Y ℂ)
    (h1 : ρ 1 = 1) (hcp : IsCompletelyPositiveOnMatrices Y ⇑ρ) (a : A) :
    (ρ (a * star a) - ρ a * star (ρ a)).PosSemidef := by
  have hstar : ∀ b : A, ρ (star b) = star (ρ b) := fun b ↦
    (ucp_map_star ρ h1 hcp b).trans (Matrix.star_eq_conjTranspose (ρ b)).symm
  have hH1 : (ρ (a * star a)).IsHermitian := by
    have h := ucp_map_star ρ h1 hcp (a * star a)
    rw [star_mul, star_star] at h
    exact h.symm
  have hH2 : (ρ a * star (ρ a)).IsHermitian := by
    rw [Matrix.star_eq_conjTranspose]
    exact Matrix.isHermitian_mul_conjTranspose_self (ρ a)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hH1.sub hH2) fun v ↦ ?_
  have key : (∑ i : Fin 2, ∑ j : Fin 2, ∑ x : Y, ∑ y : Y,
      (starRingEnd ℂ) ((![v, -(star (ρ a) *ᵥ v)] : Fin 2 → Y → ℂ) i x) *
        ρ (star ((![star a, 1] : Fin 2 → A) i) * (![star a, 1] : Fin 2 → A) j) x y *
        (![v, -(star (ρ a) *ᵥ v)] : Fin 2 → Y → ℂ) j y) =
      star v ⬝ᵥ ((ρ (a * star a) - ρ a * star (ρ a)) *ᵥ v) := by
    simp only [choiEffrosUcp_form_eq, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, star_star, star_one, mul_one, one_mul, h1, hstar, Matrix.one_mulVec,
      Matrix.mulVec_neg, dotProduct_neg, star_neg, neg_dotProduct, neg_neg]
    rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec]
    ring
  obtain ⟨him, hre⟩ := hcp 2 ![star a, 1] ![v, -(star (ρ a) *ᵥ v)]
  rw [← key]
  exact Complex.nonneg_iff.mpr ⟨hre, him.symm⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffrosUcp_kadisonSchwarz

/-- **Schwarz-defect comparison.**  The Kraus-map defect at `ρ a` is bounded by the defect of
`ψ_G ρ` at `a`. -/
theorem choiEffrosUcp_schwarzDefect_le {Y : FiniteModel} (ρ : A →ₗ[ℂ] Matrix Y Y ℂ)
    (h1 : ρ 1 = 1) (hcp : IsCompletelyPositiveOnMatrices Y ⇑ρ) (G : Y → A)
    (hG : choiEffrosPair G G = 1) (a : A) :
    ‖choiEffrosKrausMap G (ρ a * star (ρ a)) -
        choiEffrosKrausMap G (ρ a) * star (choiEffrosKrausMap G (ρ a))‖ ≤
      ‖choiEffrosKrausMap G (ρ (a * star a)) -
        choiEffrosKrausMap G (ρ a) * star (choiEffrosKrausMap G (ρ a))‖ := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hξG : choiEffrosPair (choiEffrosAct (star (ρ a)) G) G = choiEffrosKrausMap G (ρ a) := by
    have h := choiEffros_pair_act_act G (ρ a) (1 : Matrix Y Y ℂ)
    rwa [choiEffros_act_one, mul_one] at h
  have hGξ : choiEffrosPair G (choiEffrosAct (star (ρ a)) G) =
      star (choiEffrosKrausMap G (ρ a)) := by
    rw [← hξG, choiEffros_star_pair]
  have hξξ : choiEffrosPair (choiEffrosAct (star (ρ a)) G) (choiEffrosAct (star (ρ a)) G) =
      choiEffrosKrausMap G (ρ a * star (ρ a)) :=
    choiEffros_pair_act_act G (ρ a) (star (ρ a))
  have hself :
      choiEffrosPair
          (choiEffrosShift (choiEffrosAct (star (ρ a)) G) G (star (choiEffrosKrausMap G (ρ a))))
          (choiEffrosShift (choiEffrosAct (star (ρ a)) G) G (star (choiEffrosKrausMap G (ρ a)))) =
        choiEffrosKrausMap G (ρ a * star (ρ a)) -
          choiEffrosKrausMap G (ρ a) * star (choiEffrosKrausMap G (ρ a)) := by
    rw [choiEffros_pair_shift_left, choiEffros_pair_shift_right, choiEffros_pair_shift_right, hG,
      hGξ, hξG, hξξ, one_mul, sub_self, mul_zero, sub_zero]
  have hD : 0 ≤ choiEffrosKrausMap G (ρ a * star (ρ a)) -
      choiEffrosKrausMap G (ρ a) * star (choiEffrosKrausMap G (ρ a)) := by
    rw [← hself]
    exact choiEffrosUcp_pair_self_nonneg _
  have hDE : choiEffrosKrausMap G (ρ a * star (ρ a)) -
        choiEffrosKrausMap G (ρ a) * star (choiEffrosKrausMap G (ρ a)) ≤
      choiEffrosKrausMap G (ρ (a * star a)) -
        choiEffrosKrausMap G (ρ a) * star (choiEffrosKrausMap G (ρ a)) := by
    have h := choiEffrosUcp_krausMap_nonneg G (choiEffrosUcp_kadisonSchwarz ρ h1 hcp a)
    rw [map_sub] at h
    exact sub_le_sub_right (sub_nonneg.mp h) _
  exact CStarAlgebra.norm_le_norm_of_nonneg_of_le hD hDE

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffrosUcp_schwarzDefect_le

/-- If `x ≈ a a⋆` and `b ≈ a` to within `η`, and `‖b‖ ≤ ‖a‖`, then
`‖x − b b⋆‖ ≤ η (1 + 2‖a‖)`. -/
theorem choiEffrosUcp_norm_sub_mul_star_le {x a b : A} {η : ℝ} (hx : ‖x - a * star a‖ ≤ η)
    (hab : ‖b - a‖ ≤ η) (hb : ‖b‖ ≤ ‖a‖) : ‖x - b * star b‖ ≤ η * (1 + 2 * ‖a‖) := by
  have e : x - b * star b = (x - a * star a) + ((a - b) * star a + b * star (a - b)) := by
    rw [star_sub, sub_mul, mul_sub]
    abel
  have h1 : ‖(a - b) * star a‖ ≤ η * ‖a‖ := by
    refine (norm_mul_le _ _).trans ?_
    rw [norm_star, norm_sub_rev]
    exact mul_le_mul_of_nonneg_right hab (norm_nonneg a)
  have h2 : ‖b * star (a - b)‖ ≤ ‖a‖ * η := by
    refine (norm_mul_le _ _).trans ?_
    rw [norm_star, norm_sub_rev]
    exact mul_le_mul hb hab (norm_nonneg _) (norm_nonneg a)
  rw [e]
  calc ‖(x - a * star a) + ((a - b) * star a + b * star (a - b))‖
      ≤ ‖x - a * star a‖ + ‖(a - b) * star a + b * star (a - b)‖ := norm_add_le _ _
    _ ≤ ‖x - a * star a‖ + (‖(a - b) * star a‖ + ‖b * star (a - b)‖) :=
        add_le_add le_rfl (norm_add_le _ _)
    _ ≤ η + (η * ‖a‖ + ‖a‖ * η) := add_le_add hx (add_le_add h1 h2)
    _ = η * (1 + 2 * ‖a‖) := by ring

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffrosUcp_norm_sub_mul_star_le

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
