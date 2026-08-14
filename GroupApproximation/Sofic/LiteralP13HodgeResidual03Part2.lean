import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 18--26 for residual block (0, 3). -/

theorem residual_chunk_0_3_18 : initialChunk 0 3 18 = 188824566 := by
  decide

theorem residual_chunk_0_3_19 : initialChunk 0 3 19 = 245987448 := by
  decide

theorem residual_chunk_0_3_20 : initialChunk 0 3 20 = 210438669 := by
  decide

theorem residual_chunk_0_3_21 : initialChunk 0 3 21 = 205825022 := by
  decide

theorem residual_chunk_0_3_22 : initialChunk 0 3 22 = 171019683 := by
  decide

theorem residual_chunk_0_3_23 : initialChunk 0 3 23 = 65123171 := by
  decide

theorem residual_chunk_0_3_24 : initialChunk 0 3 24 = 313306180 := by
  decide

theorem residual_coeff_0_3_200 :
    (residualNumerator 0 3 200).natAbs = 49398874 := by
  decide

theorem residual_index_0_3_0 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (0 : Fin 8))) =
      (200 : Fin 293) := by
  decide

theorem residual_coeff_0_3_201 :
    (residualNumerator 0 3 201).natAbs = 292295019 := by
  decide

theorem residual_index_0_3_1 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (1 : Fin 8))) =
      (201 : Fin 293) := by
  decide

theorem residual_coeff_0_3_202 :
    (residualNumerator 0 3 202).natAbs = 19745302 := by
  decide

theorem residual_index_0_3_2 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (2 : Fin 8))) =
      (202 : Fin 293) := by
  decide

theorem residual_coeff_0_3_203 :
    (residualNumerator 0 3 203).natAbs = 9635849 := by
  decide

theorem residual_index_0_3_3 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (3 : Fin 8))) =
      (203 : Fin 293) := by
  decide

theorem residual_coeff_0_3_204 :
    (residualNumerator 0 3 204).natAbs = 1605379 := by
  decide

theorem residual_index_0_3_4 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (4 : Fin 8))) =
      (204 : Fin 293) := by
  decide

theorem residual_coeff_0_3_205 :
    (residualNumerator 0 3 205).natAbs = 123182924 := by
  decide

theorem residual_index_0_3_5 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (5 : Fin 8))) =
      (205 : Fin 293) := by
  decide

theorem residual_coeff_0_3_206 :
    (residualNumerator 0 3 206).natAbs = 10381129 := by
  decide

theorem residual_index_0_3_6 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (6 : Fin 8))) =
      (206 : Fin 293) := by
  decide

theorem residual_coeff_0_3_207 :
    (residualNumerator 0 3 207).natAbs = 9784422 := by
  decide

theorem residual_index_0_3_7 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (7 : Fin 8))) =
      (207 : Fin 293) := by
  decide

theorem residual_chunk_0_3_25 : initialChunk 0 3 25 = 516028898 := by
  unfold initialChunk
  rw [Fin.sum_univ_eight]
  rw [residual_index_0_3_0, residual_index_0_3_1, residual_index_0_3_2, residual_index_0_3_3, residual_index_0_3_4, residual_index_0_3_5, residual_index_0_3_6, residual_index_0_3_7]
  norm_num only [residual_coeff_0_3_200, residual_coeff_0_3_201, residual_coeff_0_3_202, residual_coeff_0_3_203, residual_coeff_0_3_204, residual_coeff_0_3_205, residual_coeff_0_3_206, residual_coeff_0_3_207]

theorem residual_chunk_0_3_26 : initialChunk 0 3 26 = 88593366 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_3_2 : initialPart 0 3 2 = 2005147003 := by
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
  rw [residual_chunk_0_3_18, residual_chunk_0_3_19, residual_chunk_0_3_20, residual_chunk_0_3_21, residual_chunk_0_3_22, residual_chunk_0_3_23, residual_chunk_0_3_24, residual_chunk_0_3_25, residual_chunk_0_3_26]

end LiteralP13HodgeCertificate
end GroupApproximation
