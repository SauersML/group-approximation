import GroupApproximation.Sofic.LiteralP13HodgeResidual
import GroupApproximation.Kazhdan.KazhdanUniverse

/-! # Exact unconditional P13 Hodge certificate -/

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

universe w

open ExactHodgeCertificate FiniteSupportHodgeCertificate
open LiteralP13HodgeData LiteralP13Presentation
open scoped BigOperators

noncomputable section

/-- Mutation-resistant identification of the ordered generators and all
thirteen relators of the printed P13 presentation. -/
structure ManuscriptP13Presentation : Prop where
  generator_definition : ∀ i, p13Generator i = PresentedGroup.of i
  relator_definition : ∀ i,
    p13Relator i = PresentedGroupRelatorReplay.word (p13RelatorLetters i)
  relators_definition : p13Relators = Finset.univ.image p13Relator
  presented_group_definition :
    P13 = PresentedGroup (p13Relators : Set (FreeGroup P13Generator))
  generator_0 : p13Generator 0 = E12
  generator_1 : p13Generator 1 = E13
  generator_2 : p13Generator 2 = E21
  generator_3 : p13Generator 3 = E23
  generator_4 : p13Generator 4 = E31
  generator_5 : p13Generator 5 = E32
  relator_0 : p13RelatorLetters 0 =
    [(0, true), (3, true), (0, false), (3, false), (1, false)]
  relator_1 : p13RelatorLetters 1 =
    [(1, true), (5, true), (1, false), (5, false), (0, false)]
  relator_2 : p13RelatorLetters 2 =
    [(2, true), (1, true), (2, false), (1, false), (3, false)]
  relator_3 : p13RelatorLetters 3 =
    [(3, true), (4, true), (3, false), (4, false), (2, false)]
  relator_4 : p13RelatorLetters 4 =
    [(4, true), (0, true), (4, false), (0, false), (5, false)]
  relator_5 : p13RelatorLetters 5 =
    [(5, true), (2, true), (5, false), (2, false), (4, false)]
  relator_6 : p13RelatorLetters 6 =
    [(0, true), (1, true), (0, false), (1, false)]
  relator_7 : p13RelatorLetters 7 =
    [(0, true), (5, true), (0, false), (5, false)]
  relator_8 : p13RelatorLetters 8 =
    [(1, true), (3, true), (1, false), (3, false)]
  relator_9 : p13RelatorLetters 9 =
    [(2, true), (3, true), (2, false), (3, false)]
  relator_10 : p13RelatorLetters 10 =
    [(2, true), (4, true), (2, false), (4, false)]
  relator_11 : p13RelatorLetters 11 =
    [(4, true), (5, true), (4, false), (5, false)]
  relator_12 : p13RelatorLetters 12 =
    [(0, true), (2, false), (0, true),
     (0, true), (2, false), (0, true),
     (0, true), (2, false), (0, true),
     (0, true), (2, false), (0, true)]

theorem manuscriptP13Presentation : ManuscriptP13Presentation := by
  exact {
    generator_definition := fun _ ↦ rfl
    relator_definition := fun _ ↦ rfl
    relators_definition := rfl
    presented_group_definition := rfl
    generator_0 := rfl
    generator_1 := rfl
    generator_2 := rfl
    generator_3 := rfl
    generator_4 := rfl
    generator_5 := rfl
    relator_0 := rfl
    relator_1 := rfl
    relator_2 := rfl
    relator_3 := rfl
    relator_4 := rfl
    relator_5 := rfl
    relator_6 := rfl
    relator_7 := rfl
    relator_8 := rfl
    relator_9 := rfl
    relator_10 := rfl
    relator_11 := rfl
    relator_12 := rfl
  }

private def residualBlockL1Numerator : Fin 6 → Fin 6 → ℕ
  | 0, 0 => 11626413589061
  | 0, 1 => 9037219251
  | 0, 2 => 9079445487
  | 0, 3 => 9283845417
  | 0, 4 => 8836491131
  | 0, 5 => 8235929367
  | 1, 0 => 9037219251
  | 1, 1 => 11622602362466
  | 1, 2 => 7915229999
  | 1, 3 => 6215318798
  | 1, 4 => 6701810124
  | 1, 5 => 6652740039
  | 2, 0 => 9079445487
  | 2, 1 => 7915229999
  | 2, 2 => 11624840006764
  | 2, 3 => 8331331951
  | 2, 4 => 7779090332
  | 2, 5 => 7921451991
  | 3, 0 => 9283845417
  | 3, 1 => 6215318798
  | 3, 2 => 8331331951
  | 3, 3 => 11621832714147
  | 3, 4 => 6257693699
  | 3, 5 => 6828814009
  | 4, 0 => 8836491131
  | 4, 1 => 6701810124
  | 4, 2 => 7779090332
  | 4, 3 => 6257693699
  | 4, 4 => 11622780615189
  | 4, 5 => 6642855556
  | 5, 0 => 8235929367
  | 5, 1 => 6652740039
  | 5, 2 => 7921451991
  | 5, 3 => 6828814009
  | 5, 4 => 6642855556
  | 5, 5 => 11622680190256

private theorem residual_block_natAbs :
    ∀ i k : Fin 6,
      ∑ c, (residualNumerator i k c).natAbs = residualBlockL1Numerator i k
  | 0, 0 => residual_block_natAbs_0_0
  | 0, 1 => residual_block_natAbs_0_1
  | 0, 2 => residual_block_natAbs_0_2
  | 0, 3 => residual_block_natAbs_0_3
  | 0, 4 => residual_block_natAbs_0_4
  | 0, 5 => residual_block_natAbs_0_5
  | 1, 0 => residual_block_natAbs_1_0
  | 1, 1 => residual_block_natAbs_1_1
  | 1, 2 => residual_block_natAbs_1_2
  | 1, 3 => residual_block_natAbs_1_3
  | 1, 4 => residual_block_natAbs_1_4
  | 1, 5 => residual_block_natAbs_1_5
  | 2, 0 => residual_block_natAbs_2_0
  | 2, 1 => residual_block_natAbs_2_1
  | 2, 2 => residual_block_natAbs_2_2
  | 2, 3 => residual_block_natAbs_2_3
  | 2, 4 => residual_block_natAbs_2_4
  | 2, 5 => residual_block_natAbs_2_5
  | 3, 0 => residual_block_natAbs_3_0
  | 3, 1 => residual_block_natAbs_3_1
  | 3, 2 => residual_block_natAbs_3_2
  | 3, 3 => residual_block_natAbs_3_3
  | 3, 4 => residual_block_natAbs_3_4
  | 3, 5 => residual_block_natAbs_3_5
  | 4, 0 => residual_block_natAbs_4_0
  | 4, 1 => residual_block_natAbs_4_1
  | 4, 2 => residual_block_natAbs_4_2
  | 4, 3 => residual_block_natAbs_4_3
  | 4, 4 => residual_block_natAbs_4_4
  | 4, 5 => residual_block_natAbs_4_5
  | 5, 0 => residual_block_natAbs_5_0
  | 5, 1 => residual_block_natAbs_5_1
  | 5, 2 => residual_block_natAbs_5_2
  | 5, 3 => residual_block_natAbs_5_3
  | 5, 4 => residual_block_natAbs_5_4
  | 5, 5 => residual_block_natAbs_5_5

private theorem residual_block_l1 (i k : Fin 6) :
    ∑ c, |residualCoefficient i k c| =
      (residualBlockL1Numerator i k : ℚ) / 10000000000000000 := by
  simp_rw [abs_residualCoefficient]
  rw [← Finset.sum_div]
  congr 1
  exact_mod_cast residual_block_natAbs i k

private theorem residual_row_bound (i : Fin 6) :
    ∑ k, ∑ c, |residualCoefficient i k c| ≤
      (11670886519714 / 10000000000000000 : ℚ) := by
  simp_rw [residual_block_l1]
  fin_cases i <;>
    norm_num [Fin.sum_univ_six, residualBlockL1Numerator]

private theorem residual_column_bound (k : Fin 6) :
    ∑ i, ∑ c, |residualCoefficient i k c| ≤
      (11670886519714 / 10000000000000000 : ℚ) := by
  simp_rw [residual_block_l1]
  fin_cases k <;>
    norm_num [Fin.sum_univ_six, residualBlockL1Numerator]

private theorem exactCertificate : Certificate LiteralP13HodgeData.D LiteralP13HodgeData.B
    LiteralP13HodgeData.q
    (fun i k ↦ coordinateSum LiteralP13HodgeData.productClass
      (residualCoefficient i k))
    (1 / 250) (11670886519714 / 10000000000000000) := by
  apply certificate_of_finite_support LiteralP13HodgeData.D
    LiteralP13HodgeData.B LiteralP13HodgeData.q
    LiteralP13HodgeData.support LiteralP13HodgeData.productClass
    LiteralP13HodgeReplay.productClassIndex
    LiteralP13HodgeData.support_inv_mul_support
    201 LiteralP13HodgeData.productClass_identity
    LiteralP13HodgeData.boundaryCoefficient
    LiteralP13HodgeData.adjointCoboundaryCoefficient
    LiteralP13HodgeData.qCoefficient residualCoefficient
  · norm_num
  · exact LiteralP13HodgeData.chain
  · exact LiteralP13HodgeData.B_eq_coordinateSum
  · exact LiteralP13HodgeData.adjoint_D_eq_coordinateSum
  · exact LiteralP13HodgeData.q_eq_coordinateSum
  · exact coefficient_identity
  · exact residual_row_bound
  · exact residual_column_bound

/-- The deliberately weakened public form of the P13 certificate.  The exact
residual arithmetic is confined to the proof of this declaration; clients
see only `Delta₁ = (1/250) I + Q⁺Q + R` and the row/column
coefficient-`ℓ1` bound `1/500` for `R`. -/
theorem cleanP13Certificate :
    Certificate LiteralP13HodgeData.D LiteralP13HodgeData.B
      LiteralP13HodgeData.q
      (fun i k ↦ coordinateSum LiteralP13HodgeData.productClass
        (residualCoefficient i k))
      (1 / 250) (1 / 500) where
  gap_pos := by norm_num
  chain := exactCertificate.chain
  decomposition := exactCertificate.decomposition
  residual_row_l1 i := (exactCertificate.residual_row_l1 i).trans (by norm_num)
  residual_column_l1 k :=
    (exactCertificate.residual_column_l1 k).trans (by norm_num)

/-- The human-facing consequence of the exact P13 sum-of-squares data:
the represented degree-one Hodge Laplacian is bounded below by `1/500`. -/
theorem p13_hodge_gap
    {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : P13 →* (E ≃ₗᵢ[ℝ] E)) (z : Fin 6 → E) :
    (1 / 500 : ℝ) * familyNormSq z ≤
      matrixEnergy rho
        (hodgeMatrix LiteralP13HodgeData.D LiteralP13HodgeData.B) z := by
  convert cleanP13Certificate.hodge_gap rho z using 1 ; norm_num

/-- Testing the clean Hodge estimate on exact coboundaries gives the clean
quadratic gap `A² ≥ (1/500) A` for the six-generator Laplacian. -/
theorem p13_generatorLaplacian_quadratic_gap
    {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : P13 →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    (1 / 500 : ℝ) * PositiveOperatorGap.energy
        (generatorLaplacianOperator p13Generator rho) x ≤
      ‖generatorLaplacianOperator p13Generator rho x‖ ^ 2 := by
  convert cleanP13Certificate.generatorLaplacian_quadratic_gap
    p13Generator rho x using 1 ; norm_num

theorem p13_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} P13 :=
  cleanP13Certificate.hasKazhdanPropertyT (by exact ⟨0⟩) p13Generator
    closure_range_p13Generator

theorem p13_hasKazhdanPropertyTReal : HasKazhdanPropertyT.{0, w} P13 :=
  p13_hasKazhdanPropertyT.liftUniverse

theorem p13_hasKazhdanPropertyTComplex :
    HasKazhdanPropertyTComplex.{0, w} P13 :=
  hasKazhdanPropertyT_iff_textbook.mp p13_hasKazhdanPropertyTReal

/-- The exact manuscript-facing conclusion for the displayed P13
presentation, simultaneously in the real and textbook complex formulations. -/
theorem manuscriptP13PropertyT :
    ManuscriptP13Presentation ∧
      HasKazhdanPropertyT.{0, w} P13 ∧
      HasKazhdanPropertyTComplex.{0, w} P13 :=
  ⟨manuscriptP13Presentation, p13_hasKazhdanPropertyTReal,
    p13_hasKazhdanPropertyTComplex⟩

end
end LiteralP13HodgeCertificate
end GroupApproximation
