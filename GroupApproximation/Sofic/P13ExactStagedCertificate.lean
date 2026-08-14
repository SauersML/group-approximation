import GroupApproximation.Sofic.P13ExactStagedResidual
import GroupApproximation.Kazhdan.KazhdanUniverse

/-! # Exact unconditional P13 Hodge certificate -/

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

universe w

open ExactHodgeCertificate FiniteSupportHodgeCertificate
open LiteralP13HodgeData LiteralP13Presentation
open scoped BigOperators

noncomputable section

/-- The explicit Kazhdan tolerance extracted from the printed rational P13
certificate. -/
noncomputable def p13Tolerance : ℝ :=
  certifiedKazhdanTolerance (I := Fin 6) (1 / 250)
    (11670886519714 / 10000000000000000)

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
  constructor <;> first | rfl | (intro <;> rfl)

def residualBlockL1Numerator : Fin 6 → Fin 6 → ℕ
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

theorem residual_block_l1 (i k : Fin 6) :
    ∑ c, |residualCoefficient i k c| =
      (residualBlockL1Numerator i k : ℚ) / 10000000000000000 := by
  simp_rw [abs_residualCoefficient]
  rw [← Finset.sum_div]
  congr 1
  exact_mod_cast residual_block_natAbs i k

theorem residual_row_bound (i : Fin 6) :
    ∑ k, ∑ c, |residualCoefficient i k c| ≤
      (11670886519714 / 10000000000000000 : ℚ) := by
  simp_rw [residual_block_l1]
  fin_cases i <;> norm_num [Fin.sum_univ_succ, residualBlockL1Numerator]

theorem residual_column_bound (k : Fin 6) :
    ∑ i, ∑ c, |residualCoefficient i k c| ≤
      (11670886519714 / 10000000000000000 : ℚ) := by
  simp_rw [residual_block_l1]
  fin_cases k <;> norm_num [Fin.sum_univ_succ, residualBlockL1Numerator]

theorem exactCertificate : Certificate LiteralP13HodgeData.D LiteralP13HodgeData.B
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

theorem p13_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} P13 :=
  exactCertificate.hasKazhdanPropertyT (by exact ⟨0⟩) p13Generator
    closure_range_p13Generator

theorem p13_isKazhdanPair :
    IsKazhdanPair.{0, 0} P13
      (generatorFinset p13Generator)
      p13Tolerance :=
  exactCertificate.isKazhdanPair (by exact ⟨0⟩) p13Generator
    closure_range_p13Generator

theorem p13_isKazhdanPairReal :
    IsKazhdanPair.{0, w} P13 (generatorFinset p13Generator) p13Tolerance :=
  p13_isKazhdanPair.liftUniverse

theorem p13_isKazhdanPairComplex :
    IsKazhdanPairComplex.{0, w} P13
      (generatorFinset p13Generator) p13Tolerance :=
  p13_isKazhdanPairReal.toComplex

theorem p13_hasKazhdanPropertyTReal : HasKazhdanPropertyT.{0, w} P13 :=
  p13_hasKazhdanPropertyT.liftUniverse

theorem p13_hasKazhdanPropertyTComplex :
    HasKazhdanPropertyTComplex.{0, w} P13 :=
  hasKazhdanPropertyT_iff_textbook.mp p13_hasKazhdanPropertyTReal

/-- Exact outer package matching the printed finite P13 certificate. -/
structure ManuscriptCertificate : Prop where
  presentation : ManuscriptP13Presentation
  relator_card : Fintype.card (Fin 13) = 13
  root_card : Fintype.card (Fin 6) = 6
  gram_row_card : Fintype.card (Fin 102) = 102
  support_card : Fintype.card (Fin 22) = 22
  product_class_card : Fintype.card (Fin 293) = 293
  q_denominator : LiteralP13HodgeData.qDenominator = 100000000
  coboundary_definition : LiteralP13HodgeData.D =
    generatorCoboundary p13Generator
  fox_boundary_definition : ∀ relator,
    LiteralP13HodgeData.B relator =
      PresentedGroupRelatorReplay.boundary p13Generator
        (p13RelatorLetters relator)
  q_coefficient_definition : ∀ row root supportIndex,
    LiteralP13HodgeData.qCoefficient row root supportIndex =
      (LiteralP13HodgeData.qNumerator row root supportIndex : ℚ) /
        LiteralP13HodgeData.qDenominator
  q_support_expansion : ∀ row root,
    LiteralP13HodgeData.q row root =
      coordinateSum LiteralP13HodgeData.support
        (LiteralP13HodgeData.qCoefficient row root)
  product_replay : ∀ a b : Fin 22,
    (LiteralP13HodgeData.support a)⁻¹ * LiteralP13HodgeData.support b =
      LiteralP13HodgeData.productClass
        (LiteralP13HodgeReplay.productClassIndex a b)
  chain : ∀ j, ∑ i, LiteralP13HodgeData.B j i * LiteralP13HodgeData.D i = 0
  coefficient_decomposition : ∀ i k c,
    hodgeCoefficient LiteralP13HodgeReplay.productClassIndex
        LiteralP13HodgeData.boundaryCoefficient
        LiteralP13HodgeData.adjointCoboundaryCoefficient i k c =
      scalarCoefficient 201 (1 / 250) i k c +
        gramCoefficient LiteralP13HodgeReplay.productClassIndex
          LiteralP13HodgeData.qCoefficient i k c +
        residualCoefficient i k c
  row_bound : ∀ i, ∑ k, ∑ c, |residualCoefficient i k c| ≤
    (11670886519714 / 10000000000000000 : ℚ)
  column_bound : ∀ k, ∑ i, ∑ c, |residualCoefficient i k c| ≤
    (11670886519714 / 10000000000000000 : ℚ)
  certificate : Certificate LiteralP13HodgeData.D LiteralP13HodgeData.B
    LiteralP13HodgeData.q
    (fun i k ↦ coordinateSum LiteralP13HodgeData.productClass
      (residualCoefficient i k))
    (1 / 250) (11670886519714 / 10000000000000000)
  residual_lt_gap :
    (11670886519714 / 10000000000000000 : ℚ) < 1 / 250
  certified_gap :
    (1 / 250 : ℚ) - 11670886519714 / 10000000000000000 =
      28329113480286 / 10000000000000000
  certified_gap_pos : (0 : ℚ) < 28329113480286 / 10000000000000000
  kazhdan_pair :
    IsKazhdanPair.{0, w} P13 (generatorFinset p13Generator) p13Tolerance
  kazhdan_pair_complex :
    IsKazhdanPairComplex.{0, w} P13
      (generatorFinset p13Generator) p13Tolerance
  propertyT : HasKazhdanPropertyT.{0, w} P13
  propertyTComplex : HasKazhdanPropertyTComplex.{0, w} P13

theorem manuscriptP13HodgeCertificate : ManuscriptCertificate := by
  refine ⟨manuscriptP13Presentation,
    by decide, by decide, by decide, by decide, by decide, rfl,
    rfl, fun _ ↦ rfl, fun _ _ _ ↦ rfl,
    LiteralP13HodgeData.q_eq_coordinateSum,
    LiteralP13HodgeData.support_inv_mul_support, LiteralP13HodgeData.chain,
    coefficient_identity, residual_row_bound, residual_column_bound,
    exactCertificate, by norm_num, by norm_num, by norm_num,
    p13_isKazhdanPairReal, p13_isKazhdanPairComplex,
    p13_hasKazhdanPropertyTReal,
    p13_hasKazhdanPropertyTComplex⟩

end
end LiteralP13HodgeCertificate
end GroupApproximation
