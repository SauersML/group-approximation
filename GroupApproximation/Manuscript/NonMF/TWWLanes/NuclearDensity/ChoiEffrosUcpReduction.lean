import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.ChoiEffrosUcpSchwarz
import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.ChoiEffrosUcpStatement
import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.ChoiEffrosReduction
import GroupApproximation.Analysis.UCPContractiveMatrix
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-28c, part 4: `ChoiEffrosUcpKrausStatement → ChoiEffrosKrausCPAP`

Let `K` bound `‖a‖` on `F`, and set `η = δ / (1 + 2K)`.  Run the Statement on `F ∪ F F⋆` at
tolerance `η`.

* Contractivity and star preservation of `ρ` come from `ucp_norm_le` and `ucp_map_star`.
* Contractivity of `ψ_G` is `choiEffrosUcp_norm_krausMap_le`.
* The approximation on `F` is inherited, since `η ≤ δ`.
* For the Schwarz defect, `choiEffrosUcp_schwarzDefect_le` bounds it by
  `‖ψ_G ρ(a a⋆) − ψ_G ρ(a) (ψ_G ρ a)⋆‖`, and `choiEffrosUcp_norm_sub_mul_star_le` bounds that by
  `η (1 + 2‖a‖) ≤ δ`.

The composites feed the result into the lane nm-tww-27 endpoints.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open Matrix Quasidiagonal
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

universe u

/-- **The reduction.**  The four-clause ucp Kraus Statement gives the full
`ChoiEffrosKrausCPAP`. -/
theorem choiEffrosKrausCPAP_of_ucpKraus {A : Type u} [CStarAlgebra A]
    (h : ChoiEffrosUcpKrausStatement A) : ChoiEffrosKrausCPAP A := by
  classical
  intro F δ hδ
  obtain ⟨K, hK0, hKa⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ a ∈ F, ‖a‖ ≤ K :=
    ⟨∑ a ∈ F, ‖a‖, Finset.sum_nonneg fun a _ ↦ norm_nonneg a,
      fun a ha ↦ Finset.single_le_sum (f := fun x ↦ ‖x‖) (fun x _ ↦ norm_nonneg x) ha⟩
  have hpos : 0 < 1 + 2 * K := by linarith
  obtain ⟨η, hη0, hηδ, hηmul⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧ η * (1 + 2 * K) = δ :=
    ⟨δ / (1 + 2 * K), div_pos hδ hpos, div_le_self hδ.le (by linarith),
      div_mul_cancel₀ δ hpos.ne'⟩
  obtain ⟨Y, ρ, G, hρ1, hρcp, hG, happrox⟩ := h (F ∪ F.image fun a ↦ a * star a) η hη0
  have hρc : ∀ b : A, ‖ρ b‖ ≤ ‖b‖ := ucp_norm_le ρ hρ1 hρcp
  have hρs : ∀ b : A, ρ (star b) = star (ρ b) := fun b ↦
    (ucp_map_star ρ hρ1 hρcp b).trans (Matrix.star_eq_conjTranspose (ρ b)).symm
  refine ⟨Y, ρ, G, hρ1, hρcp, hρc, hρs, hG, choiEffrosUcp_norm_krausMap_le G hG,
    fun a ha ↦ (happrox a (Finset.mem_union_left _ ha)).trans hηδ, fun a ha ↦ ?_⟩
  have hx : ‖choiEffrosKrausMap G (ρ (a * star a)) - a * star a‖ ≤ η :=
    happrox (a * star a)
      (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun a ↦ a * star a) ha))
  have hab : ‖choiEffrosKrausMap G (ρ a) - a‖ ≤ η := happrox a (Finset.mem_union_left _ ha)
  have hb : ‖choiEffrosKrausMap G (ρ a)‖ ≤ ‖a‖ :=
    (choiEffrosUcp_norm_krausMap_le G hG (ρ a)).trans (hρc a)
  refine ((choiEffrosUcp_schwarzDefect_le ρ hρ1 hρcp G hG a).trans
    (choiEffrosUcp_norm_sub_mul_star_le hx hab hb)).trans ?_
  rw [← hηmul]
  exact mul_le_mul_of_nonneg_left (by linarith [hKa a ha]) hη0.le

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffrosKrausCPAP_of_ucpKraus

/-- **The lane nm-tww-28c endpoint.**  `ChoiEffrosUcpKrausStatement` for nuclear algebras, together
with `ContractionSqrtCommutatorStatement`, gives `NuclearDensityGapStatement`. -/
theorem choiEffrosUcp_nuclearDensityGapStatement
    (hkraus : ∀ (A : Type u) (_ : CStarAlgebra A),
      CStarExactness.IsNuclearCStarAlgebra A → ChoiEffrosUcpKrausStatement A)
    (hsqrt : ContractionSqrtCommutatorStatement) : NuclearDensityGapStatement.{u} :=
  choiEffros_nuclearDensityGapStatement
    (fun A inst hn ↦ @choiEffrosKrausCPAP_of_ucpKraus A inst (hkraus A inst hn)) hsqrt

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffrosUcp_nuclearDensityGapStatement

/-- **The composite.**  The same two Statements give
`NuclearAmenable.NuclearTraceApproxDensityStatement`. -/
theorem choiEffrosUcp_nuclearTraceApproxDensityStatement
    (hkraus : ∀ (A : Type u) (_ : CStarAlgebra A),
      CStarExactness.IsNuclearCStarAlgebra A → ChoiEffrosUcpKrausStatement A)
    (hsqrt : ContractionSqrtCommutatorStatement) :
    NuclearAmenable.NuclearTraceApproxDensityStatement.{u} :=
  choiEffros_nuclearTraceApproxDensityStatement
    (fun A inst hn ↦ @choiEffrosKrausCPAP_of_ucpKraus A inst (hkraus A inst hn)) hsqrt

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.choiEffrosUcp_nuclearTraceApproxDensityStatement

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
