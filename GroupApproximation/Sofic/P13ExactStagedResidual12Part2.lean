import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 18--26 for residual block (1, 2). -/

theorem residual_chunk_1_2_18 : initialChunk 1 2 18 = 180769251 := by
  decide

theorem residual_chunk_1_2_19 : initialChunk 1 2 19 = 85380294 := by
  decide

theorem residual_chunk_1_2_20 : initialChunk 1 2 20 = 210581200 := by
  decide

theorem residual_chunk_1_2_21 : initialChunk 1 2 21 = 155652828 := by
  decide

theorem residual_chunk_1_2_22 : initialChunk 1 2 22 = 410383987 := by
  decide

theorem residual_chunk_1_2_23 : initialChunk 1 2 23 = 192361416 := by
  decide

theorem residual_chunk_1_2_24 : initialChunk 1 2 24 = 316978246 := by
  decide

theorem residual_coeff_1_2_200 :
    (residualNumerator 1 2 200).natAbs = 61023775 := by
  decide

theorem residual_index_1_2_0 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (0 : Fin 8))) =
      (200 : Fin 293) := by
  decide

theorem residual_coeff_1_2_201 :
    (residualNumerator 1 2 201).natAbs = 169441472 := by
  decide

theorem residual_index_1_2_1 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (1 : Fin 8))) =
      (201 : Fin 293) := by
  decide

theorem residual_coeff_1_2_202 :
    (residualNumerator 1 2 202).natAbs = 94383109 := by
  decide

theorem residual_index_1_2_2 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (2 : Fin 8))) =
      (202 : Fin 293) := by
  decide

theorem residual_coeff_1_2_203 :
    (residualNumerator 1 2 203).natAbs = 48696804 := by
  decide

theorem residual_index_1_2_3 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (3 : Fin 8))) =
      (203 : Fin 293) := by
  decide

theorem residual_coeff_1_2_204 :
    (residualNumerator 1 2 204).natAbs = 52061733 := by
  decide

theorem residual_index_1_2_4 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (4 : Fin 8))) =
      (204 : Fin 293) := by
  decide

theorem residual_coeff_1_2_205 :
    (residualNumerator 1 2 205).natAbs = 1335670 := by
  decide

theorem residual_index_1_2_5 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (5 : Fin 8))) =
      (205 : Fin 293) := by
  decide

theorem residual_coeff_1_2_206 :
    (residualNumerator 1 2 206).natAbs = 49671248 := by
  decide

theorem residual_index_1_2_6 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (6 : Fin 8))) =
      (206 : Fin 293) := by
  decide

theorem residual_coeff_1_2_207 :
    (residualNumerator 1 2 207).natAbs = 2069448 := by
  decide

theorem residual_index_1_2_7 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (7 : Fin 8))) =
      (207 : Fin 293) := by
  decide

theorem residual_chunk_1_2_25 : initialChunk 1 2 25 = 478683259 := by
  unfold initialChunk
  rw [Fin.sum_univ_eight]
  rw [residual_index_1_2_0, residual_index_1_2_1, residual_index_1_2_2, residual_index_1_2_3, residual_index_1_2_4, residual_index_1_2_5, residual_index_1_2_6, residual_index_1_2_7]
  norm_num only [residual_coeff_1_2_200, residual_coeff_1_2_201, residual_coeff_1_2_202, residual_coeff_1_2_203, residual_coeff_1_2_204, residual_coeff_1_2_205, residual_coeff_1_2_206, residual_coeff_1_2_207]

theorem residual_chunk_1_2_26 : initialChunk 1 2 26 = 235937266 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_2_2 : initialPart 1 2 2 = 2266727747 := by
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
  rw [residual_chunk_1_2_18, residual_chunk_1_2_19, residual_chunk_1_2_20, residual_chunk_1_2_21, residual_chunk_1_2_22, residual_chunk_1_2_23, residual_chunk_1_2_24, residual_chunk_1_2_25, residual_chunk_1_2_26]

end LiteralP13HodgeCertificate
end GroupApproximation

