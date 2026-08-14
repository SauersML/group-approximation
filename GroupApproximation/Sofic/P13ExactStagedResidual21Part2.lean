import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 18--26 for residual block (2, 1). -/

theorem residual_chunk_2_1_18 : initialChunk 2 1 18 = 182715350 := by
  decide

theorem residual_chunk_2_1_19 : initialChunk 2 1 19 = 208132181 := by
  decide

theorem residual_chunk_2_1_20 : initialChunk 2 1 20 = 305811315 := by
  decide

theorem residual_chunk_2_1_21 : initialChunk 2 1 21 = 126585147 := by
  decide

theorem residual_chunk_2_1_22 : initialChunk 2 1 22 = 489123679 := by
  decide

theorem residual_chunk_2_1_23 : initialChunk 2 1 23 = 208555338 := by
  decide

theorem residual_chunk_2_1_24 : initialChunk 2 1 24 = 244407704 := by
  decide

theorem residual_coeff_2_1_200 :
    (residualNumerator 2 1 200).natAbs = 94383109 := by
  decide

theorem residual_index_2_1_0 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (0 : Fin 8))) =
      (200 : Fin 293) := by
  decide

theorem residual_coeff_2_1_201 :
    (residualNumerator 2 1 201).natAbs = 169441472 := by
  decide

theorem residual_index_2_1_1 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (1 : Fin 8))) =
      (201 : Fin 293) := by
  decide

theorem residual_coeff_2_1_202 :
    (residualNumerator 2 1 202).natAbs = 61023775 := by
  decide

theorem residual_index_2_1_2 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (2 : Fin 8))) =
      (202 : Fin 293) := by
  decide

theorem residual_coeff_2_1_203 :
    (residualNumerator 2 1 203).natAbs = 18603999 := by
  decide

theorem residual_index_2_1_3 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (3 : Fin 8))) =
      (203 : Fin 293) := by
  decide

theorem residual_coeff_2_1_204 :
    (residualNumerator 2 1 204).natAbs = 16894107 := by
  decide

theorem residual_index_2_1_4 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (4 : Fin 8))) =
      (204 : Fin 293) := by
  decide

theorem residual_coeff_2_1_205 :
    (residualNumerator 2 1 205).natAbs = 11594023 := by
  decide

theorem residual_index_2_1_5 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (5 : Fin 8))) =
      (205 : Fin 293) := by
  decide

theorem residual_coeff_2_1_206 :
    (residualNumerator 2 1 206).natAbs = 22166267 := by
  decide

theorem residual_index_2_1_6 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (6 : Fin 8))) =
      (206 : Fin 293) := by
  decide

theorem residual_coeff_2_1_207 :
    (residualNumerator 2 1 207).natAbs = 1316097 := by
  decide

theorem residual_index_2_1_7 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (7 : Fin 8))) =
      (207 : Fin 293) := by
  decide

theorem residual_chunk_2_1_25 : initialChunk 2 1 25 = 395422849 := by
  unfold initialChunk
  rw [Fin.sum_univ_eight]
  rw [residual_index_2_1_0, residual_index_2_1_1, residual_index_2_1_2, residual_index_2_1_3, residual_index_2_1_4, residual_index_2_1_5, residual_index_2_1_6, residual_index_2_1_7]
  norm_num only [residual_coeff_2_1_200, residual_coeff_2_1_201, residual_coeff_2_1_202, residual_coeff_2_1_203, residual_coeff_2_1_204, residual_coeff_2_1_205, residual_coeff_2_1_206, residual_coeff_2_1_207]

theorem residual_chunk_2_1_26 : initialChunk 2 1 26 = 399297308 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_1_2 : initialPart 2 1 2 = 2560050871 := by
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
  rw [residual_chunk_2_1_18, residual_chunk_2_1_19, residual_chunk_2_1_20, residual_chunk_2_1_21, residual_chunk_2_1_22, residual_chunk_2_1_23, residual_chunk_2_1_24, residual_chunk_2_1_25, residual_chunk_2_1_26]

end LiteralP13HodgeCertificate
end GroupApproximation

