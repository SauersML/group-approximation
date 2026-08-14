import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 18--26 for residual block (5, 3). -/

theorem residual_chunk_5_3_18 : initialChunk 5 3 18 = 133743392 := by
  decide

theorem residual_chunk_5_3_19 : initialChunk 5 3 19 = 191283858 := by
  decide

theorem residual_chunk_5_3_20 : initialChunk 5 3 20 = 261171430 := by
  decide

theorem residual_chunk_5_3_21 : initialChunk 5 3 21 = 52158626 := by
  decide

theorem residual_chunk_5_3_22 : initialChunk 5 3 22 = 325417080 := by
  decide

theorem residual_chunk_5_3_23 : initialChunk 5 3 23 = 141139703 := by
  decide

theorem residual_chunk_5_3_24 : initialChunk 5 3 24 = 284861594 := by
  decide

theorem residual_coeff_5_3_200 :
    (residualNumerator 5 3 200).natAbs = 1101114 := by
  decide

theorem residual_index_5_3_0 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (0 : Fin 8))) =
      (200 : Fin 293) := by
  decide

theorem residual_coeff_5_3_201 :
    (residualNumerator 5 3 201).natAbs = 128311688 := by
  decide

theorem residual_index_5_3_1 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (1 : Fin 8))) =
      (201 : Fin 293) := by
  decide

theorem residual_coeff_5_3_202 :
    (residualNumerator 5 3 202).natAbs = 120853527 := by
  decide

theorem residual_index_5_3_2 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (2 : Fin 8))) =
      (202 : Fin 293) := by
  decide

theorem residual_coeff_5_3_203 :
    (residualNumerator 5 3 203).natAbs = 27713410 := by
  decide

theorem residual_index_5_3_3 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (3 : Fin 8))) =
      (203 : Fin 293) := by
  decide

theorem residual_coeff_5_3_204 :
    (residualNumerator 5 3 204).natAbs = 6751296 := by
  decide

theorem residual_index_5_3_4 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (4 : Fin 8))) =
      (204 : Fin 293) := by
  decide

theorem residual_coeff_5_3_205 :
    (residualNumerator 5 3 205).natAbs = 90202844 := by
  decide

theorem residual_index_5_3_5 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (5 : Fin 8))) =
      (205 : Fin 293) := by
  decide

theorem residual_coeff_5_3_206 :
    (residualNumerator 5 3 206).natAbs = 50533931 := by
  decide

theorem residual_index_5_3_6 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (6 : Fin 8))) =
      (206 : Fin 293) := by
  decide

theorem residual_coeff_5_3_207 :
    (residualNumerator 5 3 207).natAbs = 5321278 := by
  decide

theorem residual_index_5_3_7 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (7 : Fin 8))) =
      (207 : Fin 293) := by
  decide

theorem residual_chunk_5_3_25 : initialChunk 5 3 25 = 430789088 := by
  unfold initialChunk
  rw [Fin.sum_univ_eight]
  rw [residual_index_5_3_0, residual_index_5_3_1, residual_index_5_3_2, residual_index_5_3_3, residual_index_5_3_4, residual_index_5_3_5, residual_index_5_3_6, residual_index_5_3_7]
  norm_num only [residual_coeff_5_3_200, residual_coeff_5_3_201, residual_coeff_5_3_202, residual_coeff_5_3_203, residual_coeff_5_3_204, residual_coeff_5_3_205, residual_coeff_5_3_206, residual_coeff_5_3_207]

theorem residual_chunk_5_3_26 : initialChunk 5 3 26 = 151147180 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_3_2 : initialPart 5 3 2 = 1971711951 := by
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
  rw [residual_chunk_5_3_18, residual_chunk_5_3_19, residual_chunk_5_3_20, residual_chunk_5_3_21, residual_chunk_5_3_22, residual_chunk_5_3_23, residual_chunk_5_3_24, residual_chunk_5_3_25, residual_chunk_5_3_26]

end LiteralP13HodgeCertificate
end GroupApproximation
