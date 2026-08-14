import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 18--26 for residual block (1, 3). -/

theorem residual_chunk_1_3_18 : initialChunk 1 3 18 = 194170259 := by
  decide

theorem residual_chunk_1_3_19 : initialChunk 1 3 19 = 184257405 := by
  decide

theorem residual_chunk_1_3_20 : initialChunk 1 3 20 = 286554708 := by
  decide

theorem residual_chunk_1_3_21 : initialChunk 1 3 21 = 187061083 := by
  decide

theorem residual_chunk_1_3_22 : initialChunk 1 3 22 = 172654955 := by
  decide

theorem residual_chunk_1_3_23 : initialChunk 1 3 23 = 159343433 := by
  decide

theorem residual_chunk_1_3_24 : initialChunk 1 3 24 = 174940482 := by
  decide

theorem residual_coeff_1_3_200 :
    (residualNumerator 1 3 200).natAbs = 39955498 := by
  decide

theorem residual_index_1_3_0 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (0 : Fin 8))) =
      (200 : Fin 293) := by
  decide

theorem residual_coeff_1_3_201 :
    (residualNumerator 1 3 201).natAbs = 58193906 := by
  decide

theorem residual_index_1_3_1 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (1 : Fin 8))) =
      (201 : Fin 293) := by
  decide

theorem residual_coeff_1_3_202 :
    (residualNumerator 1 3 202).natAbs = 43121099 := by
  decide

theorem residual_index_1_3_2 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (2 : Fin 8))) =
      (202 : Fin 293) := by
  decide

theorem residual_coeff_1_3_203 :
    (residualNumerator 1 3 203).natAbs = 5590888 := by
  decide

theorem residual_index_1_3_3 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (3 : Fin 8))) =
      (203 : Fin 293) := by
  decide

theorem residual_coeff_1_3_204 :
    (residualNumerator 1 3 204).natAbs = 9308137 := by
  decide

theorem residual_index_1_3_4 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (4 : Fin 8))) =
      (204 : Fin 293) := by
  decide

theorem residual_coeff_1_3_205 :
    (residualNumerator 1 3 205).natAbs = 104935115 := by
  decide

theorem residual_index_1_3_5 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (5 : Fin 8))) =
      (205 : Fin 293) := by
  decide

theorem residual_coeff_1_3_206 :
    (residualNumerator 1 3 206).natAbs = 15857655 := by
  decide

theorem residual_index_1_3_6 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (6 : Fin 8))) =
      (206 : Fin 293) := by
  decide

theorem residual_coeff_1_3_207 :
    (residualNumerator 1 3 207).natAbs = 1725445 := by
  decide

theorem residual_index_1_3_7 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (7 : Fin 8))) =
      (207 : Fin 293) := by
  decide

theorem residual_chunk_1_3_25 : initialChunk 1 3 25 = 278687743 := by
  unfold initialChunk
  rw [Fin.sum_univ_eight]
  rw [residual_index_1_3_0, residual_index_1_3_1, residual_index_1_3_2, residual_index_1_3_3, residual_index_1_3_4, residual_index_1_3_5, residual_index_1_3_6, residual_index_1_3_7]
  norm_num only [residual_coeff_1_3_200, residual_coeff_1_3_201, residual_coeff_1_3_202, residual_coeff_1_3_203, residual_coeff_1_3_204, residual_coeff_1_3_205, residual_coeff_1_3_206, residual_coeff_1_3_207]

theorem residual_chunk_1_3_26 : initialChunk 1 3 26 = 92007273 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_3_2 : initialPart 1 3 2 = 1729677341 := by
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
  rw [residual_chunk_1_3_18, residual_chunk_1_3_19, residual_chunk_1_3_20, residual_chunk_1_3_21, residual_chunk_1_3_22, residual_chunk_1_3_23, residual_chunk_1_3_24, residual_chunk_1_3_25, residual_chunk_1_3_26]

end LiteralP13HodgeCertificate
end GroupApproximation
