import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.ChoiEffrosChoiInequality
import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.ChoiEffrosStatement
import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.CloseEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-27, part 5: `ChoiEffrosKrausCPAP → IsMatrixLeftBimoduleCPAP`, and the endpoint

Run `ChoiEffrosKrausCPAP` at a tolerance `η` with `η ≤ δ/2` and `√η ≤ δ/2`, and take
`ψ = ψ_G`.

* The clauses on `ρ` are inherited.
* The four algebraic clauses on `ψ` come from `ChoiEffrosKraus`.
* For the left bimodule clause, split
  `ψ(ρ a M) − a ψ(M) = (ψ(ρ a M) − ψ(ρ a) ψ(M)) + (ψ(ρ a) − a) ψ(M)`.
  Choi's inequality bounds the first term by `√η ‖M‖`, and contractivity of `ψ` bounds the
  second by `η ‖M‖`.

The endpoint composes the reduction with `nuclearDensityGapStatement_of_close` (lane nm-tww-25).
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open Matrix Quasidiagonal
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

universe u

/-- **The reduction.**  Kraus-column factorizations with small Schwarz defects give matrix
factorizations with the left bimodule clause. -/
theorem choiEffros_isMatrixLeftBimoduleCPAP {A : Type u} [CStarAlgebra A]
    (h : ChoiEffrosKrausCPAP A) : IsMatrixLeftBimoduleCPAP A := by
  intro F δ hδ
  have hδ2 : 0 < δ / 2 := half_pos hδ
  obtain ⟨η, hη, hηδ, hsqrtη⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ δ / 2 ∧ √η ≤ δ / 2 :=
    ⟨min ((δ / 2) ^ 2) (δ / 2), lt_min (pow_pos hδ2 2) hδ2, min_le_right _ _,
      (Real.sqrt_le_sqrt (min_le_left _ _)).trans_eq (Real.sqrt_sq hδ2.le)⟩
  obtain ⟨Y, ρ, G, hρ1, hρcp, hρc, hρs, hG, hcontr, happrox, hschwarz⟩ := h F η hη
  refine ⟨Y, ρ, choiEffrosKrausMap G, hρ1, hρcp, hρc, hρs, (choiEffros_krausMap_one G).trans hG,
    fun v ↦ ⟨_, choiEffros_krausMap_vecMulVec G v⟩, choiEffros_krausMap_star G,
    fun a ha ↦ (happrox a ha).trans (hηδ.trans (half_le_self_iff.mpr hδ.le)), ?_⟩
  intro a ha M
  have h1 := choiEffros_norm_krausMap_mul_sub_le G hG hcontr (ρ a) M
  have h2 := (Real.sqrt_le_sqrt (hschwarz a ha)).trans hsqrtη
  have h3 : ‖(choiEffrosKrausMap G (ρ a) - a) * choiEffrosKrausMap G M‖ ≤ δ / 2 * ‖M‖ :=
    (norm_mul_le _ _).trans
      (mul_le_mul ((happrox a ha).trans hηδ) (hcontr M) (norm_nonneg _) hδ2.le)
  have e : choiEffrosKrausMap G (ρ a * M) - a * choiEffrosKrausMap G M =
      (choiEffrosKrausMap G (ρ a * M) - choiEffrosKrausMap G (ρ a) * choiEffrosKrausMap G M) +
        (choiEffrosKrausMap G (ρ a) - a) * choiEffrosKrausMap G M := by
    rw [sub_mul]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h4 : δ / 2 * ‖M‖ + δ / 2 * ‖M‖ = δ * ‖M‖ := by ring
  exact (add_le_add (h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg M))) h3).trans_eq h4

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffros_isMatrixLeftBimoduleCPAP

/-- **The lane nm-tww-27 endpoint.**  `ChoiEffrosKrausCPAP` for nuclear algebras, together with
`ContractionSqrtCommutatorStatement`, gives `NuclearDensityGapStatement`. -/
theorem choiEffros_nuclearDensityGapStatement
    (hkraus : ∀ (A : Type u) (_ : CStarAlgebra A),
      CStarExactness.IsNuclearCStarAlgebra A → ChoiEffrosKrausCPAP A)
    (hsqrt : ContractionSqrtCommutatorStatement) : NuclearDensityGapStatement.{u} :=
  nuclearDensityGapStatement_of_close
    (fun A inst hn ↦ @choiEffros_isMatrixLeftBimoduleCPAP A inst (hkraus A inst hn)) hsqrt

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffros_nuclearDensityGapStatement

/-- **The composite.**  The same two Statements give
`NuclearAmenable.NuclearTraceApproxDensityStatement`. -/
theorem choiEffros_nuclearTraceApproxDensityStatement
    (hkraus : ∀ (A : Type u) (_ : CStarAlgebra A),
      CStarExactness.IsNuclearCStarAlgebra A → ChoiEffrosKrausCPAP A)
    (hsqrt : ContractionSqrtCommutatorStatement) :
    NuclearAmenable.NuclearTraceApproxDensityStatement.{u} :=
  nuclearTraceApproxDensityStatement_of_close
    (fun A inst hn ↦ @choiEffros_isMatrixLeftBimoduleCPAP A inst (hkraus A inst hn)) hsqrt

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffros_nuclearTraceApproxDensityStatement

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
