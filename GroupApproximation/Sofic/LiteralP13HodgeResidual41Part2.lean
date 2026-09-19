import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 18--26 for residual block (4, 1). -/

theorem residual_chunk_4_1_18 : initialChunk 4 1 18 = 76454590 := by
  decide

theorem residual_chunk_4_1_19 : initialChunk 4 1 19 = 206754680 := by
  decide

theorem residual_chunk_4_1_20 : initialChunk 4 1 20 = 442397605 := by
  decide

theorem residual_chunk_4_1_21 : initialChunk 4 1 21 = 230217397 := by
  decide

theorem residual_chunk_4_1_22 : initialChunk 4 1 22 = 271916344 := by
  decide

theorem residual_chunk_4_1_23 : initialChunk 4 1 23 = 227693527 := by
  decide

theorem residual_chunk_4_1_24 : initialChunk 4 1 24 = 258818321 := by
  decide

theorem residual_coeff_4_1_200 :
    (residualNumerator 4 1 200).natAbs = 45081335 := by
  decide

theorem residual_index_4_1_0 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (0 : Fin 8))) =
      (200 : Fin 293) := by
  decide

theorem residual_coeff_4_1_201 :
    (residualNumerator 4 1 201).natAbs = 102223018 := by
  decide

theorem residual_index_4_1_1 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (1 : Fin 8))) =
      (201 : Fin 293) := by
  decide

theorem residual_coeff_4_1_202 :
    (residualNumerator 4 1 202).natAbs = 28362123 := by
  decide

theorem residual_index_4_1_2 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (2 : Fin 8))) =
      (202 : Fin 293) := by
  decide

theorem residual_coeff_4_1_203 :
    (residualNumerator 4 1 203).natAbs = 816662 := by
  decide

theorem residual_index_4_1_3 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (3 : Fin 8))) =
      (203 : Fin 293) := by
  decide

theorem residual_coeff_4_1_204 :
    (residualNumerator 4 1 204).natAbs = 1681617 := by
  decide

theorem residual_index_4_1_4 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (4 : Fin 8))) =
      (204 : Fin 293) := by
  decide

theorem residual_coeff_4_1_205 :
    (residualNumerator 4 1 205).natAbs = 20040737 := by
  decide

theorem residual_index_4_1_5 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (5 : Fin 8))) =
      (205 : Fin 293) := by
  decide

theorem residual_coeff_4_1_206 :
    (residualNumerator 4 1 206).natAbs = 24743688 := by
  decide

theorem residual_index_4_1_6 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (6 : Fin 8))) =
      (206 : Fin 293) := by
  decide

theorem residual_coeff_4_1_207 :
    (residualNumerator 4 1 207).natAbs = 579701 := by
  decide

theorem residual_index_4_1_7 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (7 : Fin 8))) =
      (207 : Fin 293) := by
  decide

theorem residual_chunk_4_1_25 : initialChunk 4 1 25 = 223528881 := by
  unfold initialChunk
  rw [Fin.sum_univ_eight]
  rw [residual_index_4_1_0, residual_index_4_1_1, residual_index_4_1_2, residual_index_4_1_3, residual_index_4_1_4, residual_index_4_1_5, residual_index_4_1_6, residual_index_4_1_7]
  norm_num only [residual_coeff_4_1_200, residual_coeff_4_1_201, residual_coeff_4_1_202, residual_coeff_4_1_203, residual_coeff_4_1_204, residual_coeff_4_1_205, residual_coeff_4_1_206, residual_coeff_4_1_207]

theorem residual_chunk_4_1_26 : initialChunk 4 1 26 = 235052462 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_1_2 : initialPart 4 1 2 = 2172833807 := by
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
  rw [residual_chunk_4_1_18, residual_chunk_4_1_19, residual_chunk_4_1_20, residual_chunk_4_1_21, residual_chunk_4_1_22, residual_chunk_4_1_23, residual_chunk_4_1_24, residual_chunk_4_1_25, residual_chunk_4_1_26]

end LiteralP13HodgeCertificate
end GroupApproximation
