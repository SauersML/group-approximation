import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 18--26 for residual block (4, 3). -/

theorem residual_chunk_4_3_18 : initialChunk 4 3 18 = 213100539 := by
  decide

theorem residual_chunk_4_3_19 : initialChunk 4 3 19 = 150305663 := by
  decide

theorem residual_chunk_4_3_20 : initialChunk 4 3 20 = 218147760 := by
  decide

theorem residual_chunk_4_3_21 : initialChunk 4 3 21 = 198376259 := by
  decide

theorem residual_chunk_4_3_22 : initialChunk 4 3 22 = 370077035 := by
  decide

theorem residual_chunk_4_3_23 : initialChunk 4 3 23 = 237577665 := by
  decide

theorem residual_chunk_4_3_24 : initialChunk 4 3 24 = 230123682 := by
  decide

theorem residual_coeff_4_3_200 :
    (residualNumerator 4 3 200).natAbs = 47028486 := by
  decide

theorem residual_index_4_3_0 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (0 : Fin 8))) =
      (200 : Fin 293) := by
  decide

theorem residual_coeff_4_3_201 :
    (residualNumerator 4 3 201).natAbs = 45246938 := by
  decide

theorem residual_index_4_3_1 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (1 : Fin 8))) =
      (201 : Fin 293) := by
  decide

theorem residual_coeff_4_3_202 :
    (residualNumerator 4 3 202).natAbs = 94816097 := by
  decide

theorem residual_index_4_3_2 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (2 : Fin 8))) =
      (202 : Fin 293) := by
  decide

theorem residual_coeff_4_3_203 :
    (residualNumerator 4 3 203).natAbs = 4250347 := by
  decide

theorem residual_index_4_3_3 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (3 : Fin 8))) =
      (203 : Fin 293) := by
  decide

theorem residual_coeff_4_3_204 :
    (residualNumerator 4 3 204).natAbs = 34399662 := by
  decide

theorem residual_index_4_3_4 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (4 : Fin 8))) =
      (204 : Fin 293) := by
  decide

theorem residual_coeff_4_3_205 :
    (residualNumerator 4 3 205).natAbs = 43224767 := by
  decide

theorem residual_index_4_3_5 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (5 : Fin 8))) =
      (205 : Fin 293) := by
  decide

theorem residual_coeff_4_3_206 :
    (residualNumerator 4 3 206).natAbs = 5165451 := by
  decide

theorem residual_index_4_3_6 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (6 : Fin 8))) =
      (206 : Fin 293) := by
  decide

theorem residual_coeff_4_3_207 :
    (residualNumerator 4 3 207).natAbs = 5518039 := by
  decide

theorem residual_index_4_3_7 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (7 : Fin 8))) =
      (207 : Fin 293) := by
  decide

theorem residual_chunk_4_3_25 : initialChunk 4 3 25 = 279649787 := by
  unfold initialChunk
  rw [Fin.sum_univ_eight]
  rw [residual_index_4_3_0, residual_index_4_3_1, residual_index_4_3_2, residual_index_4_3_3, residual_index_4_3_4, residual_index_4_3_5, residual_index_4_3_6, residual_index_4_3_7]
  norm_num only [residual_coeff_4_3_200, residual_coeff_4_3_201, residual_coeff_4_3_202, residual_coeff_4_3_203, residual_coeff_4_3_204, residual_coeff_4_3_205, residual_coeff_4_3_206, residual_coeff_4_3_207]

theorem residual_chunk_4_3_26 : initialChunk 4 3 26 = 124130421 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_3_2 : initialPart 4 3 2 = 2021488811 := by
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
  rw [residual_chunk_4_3_18, residual_chunk_4_3_19, residual_chunk_4_3_20, residual_chunk_4_3_21, residual_chunk_4_3_22, residual_chunk_4_3_23, residual_chunk_4_3_24, residual_chunk_4_3_25, residual_chunk_4_3_26]

end LiteralP13HodgeCertificate
end GroupApproximation

