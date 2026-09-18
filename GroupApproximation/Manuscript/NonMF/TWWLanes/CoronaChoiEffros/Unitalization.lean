import GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.DiagonalLift
import GroupApproximation.Analysis.LanceCPContractiveUnitalization
import GroupApproximation.Meta.AxiomGuard

/-!
# Choi--Effros into matrix-sequence coronas: unital coordinates

Lane `nm-tww-08`, step 4. The CPC coordinates of `DiagonalLift` become unital completely
positive coordinates, and they still represent `Φ`.

Proof route.
* `A` is nontrivial because the corona is (`nontrivial_of_starAlgHom_normMatrixCorona`).
  Fix a state `ω` of `A`.
* Replace each coordinate `φ n` by its additive unitalization
  `φ' n a = φ n a + ω(a) (1 - φ n 1)`. It is UCP by
  `additiveUnitalization_completelyPositive_unital`.
* The assembled sequence is `s a + ω(a) (1 - s 1)`, where `s` is the CPC assembled
  sequence. Its corona image is `Φ a + ω(a) (1 - Φ 1) = Φ a`, because `Φ` is unital.

This is simpler than the compression `ψₙ(1)^{-1/2} ψₙ(·) ψₙ(1)^{-1/2}` sketched in the
`LiftCriterion` docstring. The additive defect `1 - s 1` is already null in the corona.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace CoronaChoiEffros

open GroupApproximation.CStarExactness
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u v

variable {X : ℕ → Type v} [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
  [∀ n, Nonempty (X n)] {A : Type u} [CStarAlgebra A]

/-- Bounded matrix sequences are C-star algebras (the same instance as in the corpus). -/
local instance boundedMatrixSequenceCStarAlgebraForCoronaChoiEffrosUnital :
    CStarAlgebra (BoundedMatrixSequence X) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.boundedMatrixSequenceCStarAlgebraForCoronaChoiEffrosUnital

/-- Matrix blocks at the scoped operator norm are C-star algebras. -/
local instance matrixBlockCStarAlgebraForCoronaChoiEffrosUnital
    (Z : Type*) [Fintype Z] [DecidableEq Z] [Nonempty Z] :
    CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.matrixBlockCStarAlgebraForCoronaChoiEffrosUnital

/-- **UCP coordinates, cp-map form.** A unital `⋆`-homomorphism from a separable nuclear
C-star algebra into the matrix corona has unital completely positive matrix coordinates.
Their bounded sequence represents the homomorphism. -/
theorem exists_ucp_coordinates_lift [TopologicalSpace.SeparableSpace A]
    (hnuc : IsNuclearCStarAlgebra A) (Φ : A →⋆ₐ[ℂ] NormMatrixCStarCorona X) :
    ∃ (φ : ∀ n, A →ₗ[ℂ] Matrix (X n) (X n) ℂ) (seq : A → BoundedMatrixSequence X),
      (∀ n, φ n 1 = 1) ∧ (∀ n, IsCompletelyPositive (φ n)) ∧
        (∀ (a : A) (n : ℕ), seq a n = φ n a) ∧
          ∀ a, normMatrixCStarCoronaMk X (seq a) = Φ a := by
  haveI : Nontrivial A := nontrivial_of_starAlgHom_normMatrixCorona Φ
  obtain ⟨φ, hφ, hφCP, hq⟩ := exists_cpc_coordinates_lift hnuc Φ
  let ω : CStarState.State A := (CStarState.State.exists_star_mul_self (1 : A)).choose
  have hU : ∀ n, IsCompletelyPositive (additiveUnitalization (φ n) ω) ∧
      additiveUnitalization (φ n) ω 1 = 1 := fun n ↦
    additiveUnitalization_completelyPositive_unital (φ n) ω (hφCP n) (hφ n)
  refine ⟨fun n ↦ additiveUnitalization (φ n) ω,
    fun a ↦ assembledSeq φ hφ a + ω.toCLM a • (1 - assembledSeq φ hφ 1),
    fun n ↦ (hU n).2, fun n ↦ (hU n).1, fun a n ↦ ?_, fun a ↦ ?_⟩
  · show φ n a + ω.toCLM a • ((1 : Matrix (X n) (X n) ℂ) - φ n 1) =
      additiveUnitalization (φ n) ω a
    exact (additiveUnitalization_apply (φ n) ω a).symm
  · rw [← quotient_apply_eq_mk, map_add, map_smul, map_sub, map_one, hq a, hq 1, map_one,
      sub_self, smul_zero, add_zero]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.CoronaChoiEffros.exists_ucp_coordinates_lift

end

end CoronaChoiEffros
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
