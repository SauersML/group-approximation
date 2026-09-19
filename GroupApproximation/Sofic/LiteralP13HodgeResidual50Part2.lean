import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 18--26 for residual block (5, 0). -/

theorem residual_chunk_5_0_18 : initialChunk 5 0 18 = 194068504 := by
  decide

theorem residual_chunk_5_0_19 : initialChunk 5 0 19 = 174839924 := by
  decide

theorem residual_chunk_5_0_20 : initialChunk 5 0 20 = 161398802 := by
  decide

theorem residual_chunk_5_0_21 : initialChunk 5 0 21 = 168165449 := by
  decide

theorem residual_chunk_5_0_22 : initialChunk 5 0 22 = 311269370 := by
  decide

theorem residual_chunk_5_0_23 : initialChunk 5 0 23 = 173312213 := by
  decide

theorem residual_chunk_5_0_24 : initialChunk 5 0 24 = 175651510 := by
  decide

theorem residual_coeff_5_0_200 :
    (residualNumerator 5 0 200).natAbs = 3557539 := by
  decide

theorem residual_index_5_0_0 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (0 : Fin 8))) =
      (200 : Fin 293) := by
  decide

theorem residual_coeff_5_0_201 :
    (residualNumerator 5 0 201).natAbs = 248511520 := by
  decide

theorem residual_index_5_0_1 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (1 : Fin 8))) =
      (201 : Fin 293) := by
  decide

theorem residual_coeff_5_0_202 :
    (residualNumerator 5 0 202).natAbs = 186395120 := by
  decide

theorem residual_index_5_0_2 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (2 : Fin 8))) =
      (202 : Fin 293) := by
  decide

theorem residual_coeff_5_0_203 :
    (residualNumerator 5 0 203).natAbs = 49810260 := by
  decide

theorem residual_index_5_0_3 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (3 : Fin 8))) =
      (203 : Fin 293) := by
  decide

theorem residual_coeff_5_0_204 :
    (residualNumerator 5 0 204).natAbs = 52051822 := by
  decide

theorem residual_index_5_0_4 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (4 : Fin 8))) =
      (204 : Fin 293) := by
  decide

theorem residual_coeff_5_0_205 :
    (residualNumerator 5 0 205).natAbs = 33921055 := by
  decide

theorem residual_index_5_0_5 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (5 : Fin 8))) =
      (205 : Fin 293) := by
  decide

theorem residual_coeff_5_0_206 :
    (residualNumerator 5 0 206).natAbs = 148902243 := by
  decide

theorem residual_index_5_0_6 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (6 : Fin 8))) =
      (206 : Fin 293) := by
  decide

theorem residual_coeff_5_0_207 :
    (residualNumerator 5 0 207).natAbs = 60663667 := by
  decide

theorem residual_index_5_0_7 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (7 : Fin 8))) =
      (207 : Fin 293) := by
  decide

theorem residual_chunk_5_0_25 : initialChunk 5 0 25 = 783813226 := by
  unfold initialChunk
  rw [Fin.sum_univ_eight]
  rw [residual_index_5_0_0, residual_index_5_0_1, residual_index_5_0_2, residual_index_5_0_3, residual_index_5_0_4, residual_index_5_0_5, residual_index_5_0_6, residual_index_5_0_7]
  norm_num only [residual_coeff_5_0_200, residual_coeff_5_0_201, residual_coeff_5_0_202, residual_coeff_5_0_203, residual_coeff_5_0_204, residual_coeff_5_0_205, residual_coeff_5_0_206, residual_coeff_5_0_207]

theorem residual_chunk_5_0_26 : initialChunk 5 0 26 = 146768360 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_0_2 : initialPart 5 0 2 = 2289287358 := by
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
  rw [residual_chunk_5_0_18, residual_chunk_5_0_19, residual_chunk_5_0_20, residual_chunk_5_0_21, residual_chunk_5_0_22, residual_chunk_5_0_23, residual_chunk_5_0_24, residual_chunk_5_0_25, residual_chunk_5_0_26]

end LiteralP13HodgeCertificate
end GroupApproximation
