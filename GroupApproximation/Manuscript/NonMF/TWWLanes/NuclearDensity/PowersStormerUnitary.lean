import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.PowersStormerDilation
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-26, part 3: Powers--Størmer for a unitary commutator

Let `U` be unitary, `T ≥ 0` and `h = T²`. Apply the corpus Powers--Størmer inequality
`PowersStormer.exists_selfAdjoint_unitary_powersStormer` to `UTUᴴ ≥ 0` and `T ≥ 0`. Because
`UTUᴴ − T = [U, T] Uᴴ`, it gives
`‖UT − TU‖₂² ≤ re tr((Uh − hU) G)` with the unitary `G = Uᴴ u`.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Powers--Størmer for a unitary commutator.** -/
theorem powersStormer_unitary_commutator {U T h : Matrix n n ℂ} (hU1 : Uᴴ * U = 1)
    (hU2 : U * Uᴴ = 1) (hT : T.PosSemidef) (hTh : T * T = h) :
    ∃ G : Matrix n n ℂ, Gᴴ * G = 1 ∧ G * Gᴴ = 1 ∧
      (trace ((U * T - T * U)ᴴ * (U * T - T * U))).re ≤ (trace ((U * h - h * U) * G)).re := by
  subst hTh
  obtain ⟨u, hmem, _, hps⟩ :=
    PowersStormer.exists_selfAdjoint_unitary_powersStormer (hT.mul_mul_conjTranspose_same U) hT
  have hX : U * T * Uᴴ - T = (U * T - T * U) * Uᴴ := by
    rw [sub_mul, mul_assoc T U Uᴴ, hU2, mul_one]
  have hsq : U * T * Uᴴ * (U * T * Uᴴ) - T * T = (U * (T * T) - T * T * U) * Uᴴ := by
    rw [sub_mul, mul_assoc (T * T) U Uᴴ, hU2, mul_one]
    simp only [mul_assoc]
    rw [← mul_assoc Uᴴ U, hU1, one_mul]
  have hXs : (U * T * Uᴴ - T)ᴴ = U * T * Uᴴ - T := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hT.isHermitian.eq, ← mul_assoc]
  have hl : trace ((U * T * Uᴴ - T) * (U * T * Uᴴ - T))
      = trace ((U * T - T * U)ᴴ * (U * T - T * U)) := by
    calc trace ((U * T * Uᴴ - T) * (U * T * Uᴴ - T))
        = trace ((U * T * Uᴴ - T)ᴴ * (U * T * Uᴴ - T)) := by rw [hXs]
      _ = trace (((U * T - T * U) * Uᴴ)ᴴ * ((U * T - T * U) * Uᴴ)) := by rw [hX]
      _ = trace (U * ((U * T - T * U)ᴴ * (U * T - T * U)) * Uᴴ) := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
          simp only [mul_assoc]
      _ = trace ((U * T - T * U)ᴴ * (U * T - T * U)) :=
          ConnesTrick.trace_conj_unitary U _ hU1
  rw [hl, hsq, mul_assoc (U * (T * T) - T * T * U) Uᴴ u] at hps
  have hu1 : u * uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hmem
  have hu2 : uᴴ * u = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hmem
  refine ⟨Uᴴ * u, ?_, ?_, hps⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc,
      ← mul_assoc U Uᴴ u, hU2, one_mul, hu2]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, mul_assoc,
      ← mul_assoc u uᴴ U, hu1, one_mul, hU1]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_unitary_commutator

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
