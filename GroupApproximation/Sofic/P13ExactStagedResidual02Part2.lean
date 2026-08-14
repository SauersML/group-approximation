import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 18--26 for residual block (0, 2). -/

theorem residual_chunk_0_2_18 : initialChunk 0 2 18 = 413331211 := by
  decide

theorem residual_chunk_0_2_19 : initialChunk 0 2 19 = 162324414 := by
  decide

theorem residual_chunk_0_2_20 : initialChunk 0 2 20 = 296005168 := by
  decide

theorem residual_chunk_0_2_21 : initialChunk 0 2 21 = 267786390 := by
  decide

theorem residual_chunk_0_2_22 : initialChunk 0 2 22 = 268761544 := by
  decide

theorem residual_chunk_0_2_23 : initialChunk 0 2 23 = 110852041 := by
  decide

theorem residual_chunk_0_2_24 : initialChunk 0 2 24 = 268422398 := by
  decide

theorem residual_coeff_0_2_200 :
    (residualNumerator 0 2 200).natAbs = 130519120 := by
  decide

theorem residual_index_0_2_0 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (0 : Fin 8))) =
      (200 : Fin 293) := by
  decide

theorem residual_coeff_0_2_201 :
    (residualNumerator 0 2 201).natAbs = 80866506 := by
  decide

theorem residual_index_0_2_1 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (1 : Fin 8))) =
      (201 : Fin 293) := by
  decide

theorem residual_coeff_0_2_202 :
    (residualNumerator 0 2 202).natAbs = 92094366 := by
  decide

theorem residual_index_0_2_2 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (2 : Fin 8))) =
      (202 : Fin 293) := by
  decide

theorem residual_coeff_0_2_203 :
    (residualNumerator 0 2 203).natAbs = 16646177 := by
  decide

theorem residual_index_0_2_3 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (3 : Fin 8))) =
      (203 : Fin 293) := by
  decide

theorem residual_coeff_0_2_204 :
    (residualNumerator 0 2 204).natAbs = 303099 := by
  decide

theorem residual_index_0_2_4 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (4 : Fin 8))) =
      (204 : Fin 293) := by
  decide

theorem residual_coeff_0_2_205 :
    (residualNumerator 0 2 205).natAbs = 82459235 := by
  decide

theorem residual_index_0_2_5 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (5 : Fin 8))) =
      (205 : Fin 293) := by
  decide

theorem residual_coeff_0_2_206 :
    (residualNumerator 0 2 206).natAbs = 29751262 := by
  decide

theorem residual_index_0_2_6 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (6 : Fin 8))) =
      (206 : Fin 293) := by
  decide

theorem residual_coeff_0_2_207 :
    (residualNumerator 0 2 207).natAbs = 21108371 := by
  decide

theorem residual_index_0_2_7 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (7 : Fin 8))) =
      (207 : Fin 293) := by
  decide

theorem residual_chunk_0_2_25 : initialChunk 0 2 25 = 453748136 := by
  unfold initialChunk
  rw [Fin.sum_univ_eight]
  rw [residual_index_0_2_0, residual_index_0_2_1, residual_index_0_2_2, residual_index_0_2_3, residual_index_0_2_4, residual_index_0_2_5, residual_index_0_2_6, residual_index_0_2_7]
  norm_num only [residual_coeff_0_2_200, residual_coeff_0_2_201, residual_coeff_0_2_202, residual_coeff_0_2_203, residual_coeff_0_2_204, residual_coeff_0_2_205, residual_coeff_0_2_206, residual_coeff_0_2_207]

theorem residual_chunk_0_2_26 : initialChunk 0 2 26 = 293319762 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_2_2 : initialPart 0 2 2 = 2534551064 := by
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
  rw [residual_chunk_0_2_18, residual_chunk_0_2_19, residual_chunk_0_2_20, residual_chunk_0_2_21, residual_chunk_0_2_22, residual_chunk_0_2_23, residual_chunk_0_2_24, residual_chunk_0_2_25, residual_chunk_0_2_26]

end LiteralP13HodgeCertificate
end GroupApproximation

