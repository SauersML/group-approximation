import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 18--26 for residual block (3, 5). -/

theorem residual_chunk_3_5_18 : initialChunk 3 5 18 = 116783953 := by
  decide

theorem residual_chunk_3_5_19 : initialChunk 3 5 19 = 127247919 := by
  decide

theorem residual_chunk_3_5_20 : initialChunk 3 5 20 = 164274098 := by
  decide

theorem residual_chunk_3_5_21 : initialChunk 3 5 21 = 151986269 := by
  decide

theorem residual_chunk_3_5_22 : initialChunk 3 5 22 = 282644102 := by
  decide

theorem residual_chunk_3_5_23 : initialChunk 3 5 23 = 146108616 := by
  decide

theorem residual_chunk_3_5_24 : initialChunk 3 5 24 = 243298210 := by
  decide

theorem residual_coeff_3_5_200 :
    (residualNumerator 3 5 200).natAbs = 120853527 := by
  decide

theorem residual_index_3_5_0 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (0 : Fin 8))) =
      (200 : Fin 293) := by
  decide

theorem residual_coeff_3_5_201 :
    (residualNumerator 3 5 201).natAbs = 128311688 := by
  decide

theorem residual_index_3_5_1 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (1 : Fin 8))) =
      (201 : Fin 293) := by
  decide

theorem residual_coeff_3_5_202 :
    (residualNumerator 3 5 202).natAbs = 1101114 := by
  decide

theorem residual_index_3_5_2 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (2 : Fin 8))) =
      (202 : Fin 293) := by
  decide

theorem residual_coeff_3_5_203 :
    (residualNumerator 3 5 203).natAbs = 7107253 := by
  decide

theorem residual_index_3_5_3 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (3 : Fin 8))) =
      (203 : Fin 293) := by
  decide

theorem residual_coeff_3_5_204 :
    (residualNumerator 3 5 204).natAbs = 30137946 := by
  decide

theorem residual_index_3_5_4 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (4 : Fin 8))) =
      (204 : Fin 293) := by
  decide

theorem residual_coeff_3_5_205 :
    (residualNumerator 3 5 205).natAbs = 95909090 := by
  decide

theorem residual_index_3_5_5 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (5 : Fin 8))) =
      (205 : Fin 293) := by
  decide

theorem residual_coeff_3_5_206 :
    (residualNumerator 3 5 206).natAbs = 21542245 := by
  decide

theorem residual_index_3_5_6 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (6 : Fin 8))) =
      (206 : Fin 293) := by
  decide

theorem residual_coeff_3_5_207 :
    (residualNumerator 3 5 207).natAbs = 18603376 := by
  decide

theorem residual_index_3_5_7 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (7 : Fin 8))) =
      (207 : Fin 293) := by
  decide

theorem residual_chunk_3_5_25 : initialChunk 3 5 25 = 423566239 := by
  unfold initialChunk
  rw [Fin.sum_univ_eight]
  rw [residual_index_3_5_0, residual_index_3_5_1, residual_index_3_5_2, residual_index_3_5_3, residual_index_3_5_4, residual_index_3_5_5, residual_index_3_5_6, residual_index_3_5_7]
  norm_num only [residual_coeff_3_5_200, residual_coeff_3_5_201, residual_coeff_3_5_202, residual_coeff_3_5_203, residual_coeff_3_5_204, residual_coeff_3_5_205, residual_coeff_3_5_206, residual_coeff_3_5_207]

theorem residual_chunk_3_5_26 : initialChunk 3 5 26 = 171963594 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_5_2 : initialPart 3 5 2 = 1827873000 := by
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
  rw [residual_chunk_3_5_18, residual_chunk_3_5_19, residual_chunk_3_5_20, residual_chunk_3_5_21, residual_chunk_3_5_22, residual_chunk_3_5_23, residual_chunk_3_5_24, residual_chunk_3_5_25, residual_chunk_3_5_26]

end LiteralP13HodgeCertificate
end GroupApproximation

