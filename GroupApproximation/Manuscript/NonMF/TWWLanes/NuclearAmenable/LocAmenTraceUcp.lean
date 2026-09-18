import GroupApproximation.Analysis.LanceForward
import GroupApproximation.Analysis.LanceCPContractiveUnitalization
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-29, part 2: ucp matrix factorizations of a nuclear algebra

For a nontrivial nuclear `A`, the cpc matrix factorizations from
`CStarExactness.exists_matrixModelApproximation_of_isNuclearCStarAlgebra` are made unital
on both legs.  The tool is the additive unitalization `φ + ω(·)(1 - φ 1)` from
`LanceCPContractiveUnitalization`, with its factor-four estimate on the unit ball.

A general `a ∈ F` is handled by rescaling.  With `R = ∑_{a ∈ F} ‖a‖`, test the set
`{1} ∪ (R+1)⁻¹ F` at tolerance `ε / (4 (R + 1))`.

Everything in this file is proved.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearAmenable

open CStarExactness
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

attribute [local instance] CStarExactness.matrixBlockCStarAlgebraForLanceForward

/-- **ucp matrix factorizations.**  A nontrivial nuclear C*-algebra approximately factors
through a matrix block by two unital completely positive maps. -/
theorem locAmenTrace_exists_ucpMatrixApproximation {A : Type u} [CStarAlgebra A]
    [Nontrivial A] (hnuc : IsNuclearCStarAlgebra A) (F : Finset A) (ε : ℝ) (hε : 0 < ε) :
    ∃ (Y : FiniteModel) (hY : Nonempty Y),
      letI : Nonempty Y := hY
      ∃ (ρ : A →ₗ[ℂ] Matrix Y Y ℂ) (ψ : Matrix Y Y ℂ →ₗ[ℂ] A),
        IsCompletelyPositive ρ ∧ ρ 1 = 1 ∧ IsCompletelyPositive ψ ∧ ψ 1 = 1 ∧
          ∀ a ∈ F, ‖ψ (ρ a) - a‖ ≤ ε := by
  classical
  obtain ⟨R, hR0, hRF⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ a ∈ F, ‖a‖ ≤ R :=
    ⟨∑ a ∈ F, ‖a‖, Finset.sum_nonneg fun b _ ↦ norm_nonneg b,
      fun a ha ↦ Finset.single_le_sum (f := fun b ↦ ‖b‖) (fun b _ ↦ norm_nonneg b) ha⟩
  have hR1 : 0 < R + 1 := by linarith
  have h4R : 0 < 4 * (R + 1) := mul_pos (by norm_num) hR1
  have hδ : 0 < ε / (4 * (R + 1)) := div_pos hε h4R
  let t : ℂ := ((R + 1 : ℝ) : ℂ)
  have ht : t ≠ 0 := Complex.ofReal_ne_zero.mpr hR1.ne'
  have hnorm_t : ‖t‖ = R + 1 := Complex.norm_of_nonneg hR1.le
  let G : Finset A := insert 1 (F.image fun a ↦ t⁻¹ • a)
  obtain ⟨Y, hY, down, up, hdownCP, hupCP, hdownC, hupC, hrec⟩ :=
    exists_matrixModelApproximation_of_isNuclearCStarAlgebra hnuc G (ε / (4 * (R + 1))) hδ
  letI : Nonempty Y := hY
  let omegaA : CStarState.State A := (CStarState.State.exists_star_mul_self (1 : A)).choose
  let omegaY : CStarState.State (Matrix Y Y ℂ) :=
    (CStarState.State.exists_star_mul_self (1 : Matrix Y Y ℂ)).choose
  obtain ⟨hρCP, hρ1⟩ :=
    additiveUnitalization_completelyPositive_unital down omegaA hdownCP hdownC
  obtain ⟨hψCP, hψ1⟩ :=
    additiveUnitalization_completelyPositive_unital up omegaY hupCP hupC
  refine ⟨Y, hY, additiveUnitalization down omegaA, additiveUnitalization up omegaY,
    hρCP, hρ1, hψCP, hψ1, ?_⟩
  intro a ha
  have hone : ‖up (down 1) - 1‖ ≤ ε / (4 * (R + 1)) := hrec 1 (Finset.mem_insert_self 1 _)
  have hbmem : t⁻¹ • a ∈ G := Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  have hb : ‖t⁻¹ • a‖ ≤ 1 := by
    rw [norm_smul, norm_inv, hnorm_t, inv_mul_le_iff₀ hR1, mul_one]
    linarith [hRF a ha]
  have hfour := norm_additiveUnitalization_comp_sub_le_four_mul down up omegaA omegaY
    hdownCP hupCP hdownC hupC hone (t⁻¹ • a) hb (hrec _ hbmem)
  have hlin : additiveUnitalization up omegaY (additiveUnitalization down omegaA a) - a =
      t • (additiveUnitalization up omegaY (additiveUnitalization down omegaA (t⁻¹ • a)) -
        t⁻¹ • a) := by
    rw [map_smul, map_smul, ← smul_sub, smul_inv_smul₀ ht]
  have hkey : (R + 1) * (4 * (ε / (4 * (R + 1)))) = ε := by
    rw [← mul_assoc, mul_comm (R + 1) 4, mul_div_cancel₀ ε h4R.ne']
  calc ‖additiveUnitalization up omegaY (additiveUnitalization down omegaA a) - a‖
      = (R + 1) * ‖additiveUnitalization up omegaY
          (additiveUnitalization down omegaA (t⁻¹ • a)) - t⁻¹ • a‖ := by
        rw [hlin, norm_smul, hnorm_t]
    _ ≤ (R + 1) * (4 * (ε / (4 * (R + 1)))) := mul_le_mul_of_nonneg_left hfour hR1.le
    _ = ε := hkey

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.locAmenTrace_exists_ucpMatrixApproximation

end

end Manuscript.NonMF.TWWLanes.NuclearAmenable
end GroupApproximation
