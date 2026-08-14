import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 18--26 for residual block (0, 4). -/

theorem residual_chunk_0_4_18 : initialChunk 0 4 18 = 92877131 := by
  decide

theorem residual_chunk_0_4_19 : initialChunk 0 4 19 = 138516704 := by
  decide

theorem residual_chunk_0_4_20 : initialChunk 0 4 20 = 309507535 := by
  decide

theorem residual_chunk_0_4_21 : initialChunk 0 4 21 = 148104674 := by
  decide

theorem residual_chunk_0_4_22 : initialChunk 0 4 22 = 285071751 := by
  decide

theorem residual_chunk_0_4_23 : initialChunk 0 4 23 = 235545606 := by
  decide

theorem residual_chunk_0_4_24 : initialChunk 0 4 24 = 383155207 := by
  decide

theorem residual_coeff_0_4_200 :
    (residualNumerator 0 4 200).natAbs = 53841800 := by
  decide

theorem residual_index_0_4_0 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (0 : Fin 8))) =
      (200 : Fin 293) := by
  decide

theorem residual_coeff_0_4_201 :
    (residualNumerator 0 4 201).natAbs = 2511614 := by
  decide

theorem residual_index_0_4_1 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (1 : Fin 8))) =
      (201 : Fin 293) := by
  decide

theorem residual_coeff_0_4_202 :
    (residualNumerator 0 4 202).natAbs = 86366320 := by
  decide

theorem residual_index_0_4_2 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (2 : Fin 8))) =
      (202 : Fin 293) := by
  decide

theorem residual_coeff_0_4_203 :
    (residualNumerator 0 4 203).natAbs = 3496804 := by
  decide

theorem residual_index_0_4_3 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (3 : Fin 8))) =
      (203 : Fin 293) := by
  decide

theorem residual_coeff_0_4_204 :
    (residualNumerator 0 4 204).natAbs = 90168629 := by
  decide

theorem residual_index_0_4_4 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (4 : Fin 8))) =
      (204 : Fin 293) := by
  decide

theorem residual_coeff_0_4_205 :
    (residualNumerator 0 4 205).natAbs = 219516041 := by
  decide

theorem residual_index_0_4_5 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (5 : Fin 8))) =
      (205 : Fin 293) := by
  decide

theorem residual_coeff_0_4_206 :
    (residualNumerator 0 4 206).natAbs = 6054893 := by
  decide

theorem residual_index_0_4_6 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (6 : Fin 8))) =
      (206 : Fin 293) := by
  decide

theorem residual_coeff_0_4_207 :
    (residualNumerator 0 4 207).natAbs = 15723982 := by
  decide

theorem residual_index_0_4_7 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (7 : Fin 8))) =
      (207 : Fin 293) := by
  decide

theorem residual_chunk_0_4_25 : initialChunk 0 4 25 = 477680083 := by
  unfold initialChunk
  rw [Fin.sum_univ_eight]
  rw [residual_index_0_4_0, residual_index_0_4_1, residual_index_0_4_2, residual_index_0_4_3, residual_index_0_4_4, residual_index_0_4_5, residual_index_0_4_6, residual_index_0_4_7]
  norm_num only [residual_coeff_0_4_200, residual_coeff_0_4_201, residual_coeff_0_4_202, residual_coeff_0_4_203, residual_coeff_0_4_204, residual_coeff_0_4_205, residual_coeff_0_4_206, residual_coeff_0_4_207]

theorem residual_chunk_0_4_26 : initialChunk 0 4 26 = 233034742 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_4_2 : initialPart 0 4 2 = 2303493433 := by
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
  rw [residual_chunk_0_4_18, residual_chunk_0_4_19, residual_chunk_0_4_20, residual_chunk_0_4_21, residual_chunk_0_4_22, residual_chunk_0_4_23, residual_chunk_0_4_24, residual_chunk_0_4_25, residual_chunk_0_4_26]

end LiteralP13HodgeCertificate
end GroupApproximation

