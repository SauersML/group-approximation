import GroupApproximation.Sofic.LiteralP13HodgeResidual

/-! # Exact unconditional P13 Hodge certificate -/

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

universe w

open ExactHodgeCertificate FiniteSupportHodgeCertificate
open LiteralP13HodgeData LiteralP13Presentation
open scoped BigOperators

noncomputable section

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

theorem p13_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} P13 :=
  cleanP13Certificate.hasKazhdanPropertyT (by exact ⟨0⟩) p13Generator
    closure_range_p13Generator

end
end LiteralP13HodgeCertificate
end GroupApproximation
