import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 18--26 for residual block (2, 3). -/

theorem residual_chunk_2_3_18 : initialChunk 2 3 18 = 389215573 := by
  decide

theorem residual_chunk_2_3_19 : initialChunk 2 3 19 = 349586579 := by
  decide

theorem residual_chunk_2_3_20 : initialChunk 2 3 20 = 355937713 := by
  decide

theorem residual_chunk_2_3_21 : initialChunk 2 3 21 = 222078362 := by
  decide

theorem residual_chunk_2_3_22 : initialChunk 2 3 22 = 223944490 := by
  decide

theorem residual_chunk_2_3_23 : initialChunk 2 3 23 = 94029742 := by
  decide

theorem residual_chunk_2_3_24 : initialChunk 2 3 24 = 290803966 := by
  decide

theorem residual_coeff_2_3_200 :
    (residualNumerator 2 3 200).natAbs = 40540963 := by
  decide

theorem residual_index_2_3_0 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (0 : Fin 8))) =
      (200 : Fin 293) := by
  decide

theorem residual_coeff_2_3_201 :
    (residualNumerator 2 3 201).natAbs = 132884849 := by
  decide

theorem residual_index_2_3_1 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (1 : Fin 8))) =
      (201 : Fin 293) := by
  decide

theorem residual_coeff_2_3_202 :
    (residualNumerator 2 3 202).natAbs = 122736390 := by
  decide

theorem residual_index_2_3_2 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (2 : Fin 8))) =
      (202 : Fin 293) := by
  decide

theorem residual_coeff_2_3_203 :
    (residualNumerator 2 3 203).natAbs = 20730271 := by
  decide

theorem residual_index_2_3_3 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (3 : Fin 8))) =
      (203 : Fin 293) := by
  decide

theorem residual_coeff_2_3_204 :
    (residualNumerator 2 3 204).natAbs = 30089352 := by
  decide

theorem residual_index_2_3_4 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (4 : Fin 8))) =
      (204 : Fin 293) := by
  decide

theorem residual_coeff_2_3_205 :
    (residualNumerator 2 3 205).natAbs = 91561132 := by
  decide

theorem residual_index_2_3_5 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (5 : Fin 8))) =
      (205 : Fin 293) := by
  decide

theorem residual_coeff_2_3_206 :
    (residualNumerator 2 3 206).natAbs = 14444918 := by
  decide

theorem residual_index_2_3_6 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (6 : Fin 8))) =
      (206 : Fin 293) := by
  decide

theorem residual_coeff_2_3_207 :
    (residualNumerator 2 3 207).natAbs = 3995363 := by
  decide

theorem residual_index_2_3_7 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (7 : Fin 8))) =
      (207 : Fin 293) := by
  decide

theorem residual_chunk_2_3_25 : initialChunk 2 3 25 = 456983238 := by
  unfold initialChunk
  rw [Fin.sum_univ_eight]
  rw [residual_index_2_3_0, residual_index_2_3_1, residual_index_2_3_2, residual_index_2_3_3, residual_index_2_3_4, residual_index_2_3_5, residual_index_2_3_6, residual_index_2_3_7]
  norm_num only [residual_coeff_2_3_200, residual_coeff_2_3_201, residual_coeff_2_3_202, residual_coeff_2_3_203, residual_coeff_2_3_204, residual_coeff_2_3_205, residual_coeff_2_3_206, residual_coeff_2_3_207]

theorem residual_chunk_2_3_26 : initialChunk 2 3 26 = 223639960 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_3_2 : initialPart 2 3 2 = 2606219623 := by
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
  rw [residual_chunk_2_3_18, residual_chunk_2_3_19, residual_chunk_2_3_20, residual_chunk_2_3_21, residual_chunk_2_3_22, residual_chunk_2_3_23, residual_chunk_2_3_24, residual_chunk_2_3_25, residual_chunk_2_3_26]

end LiteralP13HodgeCertificate
end GroupApproximation
