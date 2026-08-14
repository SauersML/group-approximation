import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 18--26 for residual block (1, 5). -/

theorem residual_chunk_1_5_18 : initialChunk 1 5 18 = 153320421 := by
  decide

theorem residual_chunk_1_5_19 : initialChunk 1 5 19 = 130072740 := by
  decide

theorem residual_chunk_1_5_20 : initialChunk 1 5 20 = 210165901 := by
  decide

theorem residual_chunk_1_5_21 : initialChunk 1 5 21 = 111295816 := by
  decide

theorem residual_chunk_1_5_22 : initialChunk 1 5 22 = 373411771 := by
  decide

theorem residual_chunk_1_5_23 : initialChunk 1 5 23 = 175886734 := by
  decide

theorem residual_chunk_1_5_24 : initialChunk 1 5 24 = 177327602 := by
  decide

theorem residual_coeff_1_5_200 :
    (residualNumerator 1 5 200).natAbs = 27172063 := by
  decide

theorem residual_index_1_5_0 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (0 : Fin 8))) =
      (200 : Fin 293) := by
  decide

theorem residual_coeff_1_5_201 :
    (residualNumerator 1 5 201).natAbs = 195588232 := by
  decide

theorem residual_index_1_5_1 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (1 : Fin 8))) =
      (201 : Fin 293) := by
  decide

theorem residual_coeff_1_5_202 :
    (residualNumerator 1 5 202).natAbs = 151687450 := by
  decide

theorem residual_index_1_5_2 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (2 : Fin 8))) =
      (202 : Fin 293) := by
  decide

theorem residual_coeff_1_5_203 :
    (residualNumerator 1 5 203).natAbs = 19246674 := by
  decide

theorem residual_index_1_5_3 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (3 : Fin 8))) =
      (203 : Fin 293) := by
  decide

theorem residual_coeff_1_5_204 :
    (residualNumerator 1 5 204).natAbs = 44266393 := by
  decide

theorem residual_index_1_5_4 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (4 : Fin 8))) =
      (204 : Fin 293) := by
  decide

theorem residual_coeff_1_5_205 :
    (residualNumerator 1 5 205).natAbs = 9044252 := by
  decide

theorem residual_index_1_5_5 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (5 : Fin 8))) =
      (205 : Fin 293) := by
  decide

theorem residual_coeff_1_5_206 :
    (residualNumerator 1 5 206).natAbs = 55973157 := by
  decide

theorem residual_index_1_5_6 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (6 : Fin 8))) =
      (206 : Fin 293) := by
  decide

theorem residual_coeff_1_5_207 :
    (residualNumerator 1 5 207).natAbs = 64278595 := by
  decide

theorem residual_index_1_5_7 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (7 : Fin 8))) =
      (207 : Fin 293) := by
  decide

theorem residual_chunk_1_5_25 : initialChunk 1 5 25 = 567256816 := by
  unfold initialChunk
  rw [Fin.sum_univ_eight]
  rw [residual_index_1_5_0, residual_index_1_5_1, residual_index_1_5_2, residual_index_1_5_3, residual_index_1_5_4, residual_index_1_5_5, residual_index_1_5_6, residual_index_1_5_7]
  norm_num only [residual_coeff_1_5_200, residual_coeff_1_5_201, residual_coeff_1_5_202, residual_coeff_1_5_203, residual_coeff_1_5_204, residual_coeff_1_5_205, residual_coeff_1_5_206, residual_coeff_1_5_207]

theorem residual_chunk_1_5_26 : initialChunk 1 5 26 = 143605882 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_5_2 : initialPart 1 5 2 = 2042343683 := by
  unfold initialPart
  rw [sum_fin9_explicit]
  rw [show finProdFinEquiv ((2 : Fin 4), (0 : Fin 9)) = (18 : Fin 36) by decide]
  rw [show finProdFinEquiv ((2 : Fin 4), (1 : Fin 9)) = (19 : Fin 36) by decide]
  rw [show finProdFinEquiv ((2 : Fin 4), (2 : Fin 9)) = (20 : Fin 36) by decide]
  rw [show finProdFinEquiv ((2 : Fin 4), (3 : Fin 9)) = (21 : Fin 36) by decide]
  rw [show finProdFinEquiv ((2 : Fin 4), (4 : Fin 9)) = (22 : Fin 36) by decide]
  rw [show finProdFinEquiv ((2 : Fin 4), (5 : Fin 9)) = (23 : Fin 36) by decide]
  rw [show finProdFinEquiv ((2 : Fin 4), (6 : Fin 9)) = (24 : Fin 36) by decide]
  rw [show finProdFinEquiv ((2 : Fin 4), (7 : Fin 9)) = (25 : Fin 36) by decide]
  rw [show finProdFinEquiv ((2 : Fin 4), (8 : Fin 9)) = (26 : Fin 36) by decide]
  rw [residual_chunk_1_5_18, residual_chunk_1_5_19, residual_chunk_1_5_20, residual_chunk_1_5_21, residual_chunk_1_5_22, residual_chunk_1_5_23, residual_chunk_1_5_24, residual_chunk_1_5_25, residual_chunk_1_5_26]

end LiteralP13HodgeCertificate
end GroupApproximation

