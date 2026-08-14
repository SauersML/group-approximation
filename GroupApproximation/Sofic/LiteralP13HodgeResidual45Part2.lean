import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 18--26 for residual block (4, 5). -/

theorem residual_chunk_4_5_18 : initialChunk 4 5 18 = 173558517 := by
  decide

theorem residual_chunk_4_5_19 : initialChunk 4 5 19 = 110492333 := by
  decide

theorem residual_chunk_4_5_20 : initialChunk 4 5 20 = 276290642 := by
  decide

theorem residual_chunk_4_5_21 : initialChunk 4 5 21 = 136189369 := by
  decide

theorem residual_chunk_4_5_22 : initialChunk 4 5 22 = 184474198 := by
  decide

theorem residual_chunk_4_5_23 : initialChunk 4 5 23 = 122810862 := by
  decide

theorem residual_chunk_4_5_24 : initialChunk 4 5 24 = 151851643 := by
  decide

theorem residual_coeff_4_5_200 :
    (residualNumerator 4 5 200).natAbs = 83771842 := by
  decide

theorem residual_index_4_5_0 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (0 : Fin 8))) =
      (200 : Fin 293) := by
  decide

theorem residual_coeff_4_5_201 :
    (residualNumerator 4 5 201).natAbs = 22016772 := by
  decide

theorem residual_index_4_5_1 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (1 : Fin 8))) =
      (201 : Fin 293) := by
  decide

theorem residual_coeff_4_5_202 :
    (residualNumerator 4 5 202).natAbs = 61459280 := by
  decide

theorem residual_index_4_5_2 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (2 : Fin 8))) =
      (202 : Fin 293) := by
  decide

theorem residual_coeff_4_5_203 :
    (residualNumerator 4 5 203).natAbs = 8928871 := by
  decide

theorem residual_index_4_5_3 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (3 : Fin 8))) =
      (203 : Fin 293) := by
  decide

theorem residual_coeff_4_5_204 :
    (residualNumerator 4 5 204).natAbs = 90465463 := by
  decide

theorem residual_index_4_5_4 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (4 : Fin 8))) =
      (204 : Fin 293) := by
  decide

theorem residual_coeff_4_5_205 :
    (residualNumerator 4 5 205).natAbs = 47884796 := by
  decide

theorem residual_index_4_5_5 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (5 : Fin 8))) =
      (205 : Fin 293) := by
  decide

theorem residual_coeff_4_5_206 :
    (residualNumerator 4 5 206).natAbs = 32867294 := by
  decide

theorem residual_index_4_5_6 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (6 : Fin 8))) =
      (206 : Fin 293) := by
  decide

theorem residual_coeff_4_5_207 :
    (residualNumerator 4 5 207).natAbs = 34873624 := by
  decide

theorem residual_index_4_5_7 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (7 : Fin 8))) =
      (207 : Fin 293) := by
  decide

theorem residual_chunk_4_5_25 : initialChunk 4 5 25 = 382267942 := by
  unfold initialChunk
  rw [Fin.sum_univ_eight]
  rw [residual_index_4_5_0, residual_index_4_5_1, residual_index_4_5_2, residual_index_4_5_3, residual_index_4_5_4, residual_index_4_5_5, residual_index_4_5_6, residual_index_4_5_7]
  norm_num only [residual_coeff_4_5_200, residual_coeff_4_5_201, residual_coeff_4_5_202, residual_coeff_4_5_203, residual_coeff_4_5_204, residual_coeff_4_5_205, residual_coeff_4_5_206, residual_coeff_4_5_207]

theorem residual_chunk_4_5_26 : initialChunk 4 5 26 = 143683180 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_5_2 : initialPart 4 5 2 = 1681618686 := by
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
  rw [residual_chunk_4_5_18, residual_chunk_4_5_19, residual_chunk_4_5_20, residual_chunk_4_5_21, residual_chunk_4_5_22, residual_chunk_4_5_23, residual_chunk_4_5_24, residual_chunk_4_5_25, residual_chunk_4_5_26]

end LiteralP13HodgeCertificate
end GroupApproximation
