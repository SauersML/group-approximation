import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 18--26 for residual block (5, 4). -/

theorem residual_chunk_5_4_18 : initialChunk 5 4 18 = 193007699 := by
  decide

theorem residual_chunk_5_4_19 : initialChunk 5 4 19 = 152734637 := by
  decide

theorem residual_chunk_5_4_20 : initialChunk 5 4 20 = 143467630 := by
  decide

theorem residual_chunk_5_4_21 : initialChunk 5 4 21 = 170274762 := by
  decide

theorem residual_chunk_5_4_22 : initialChunk 5 4 22 = 206231319 := by
  decide

theorem residual_chunk_5_4_23 : initialChunk 5 4 23 = 171049298 := by
  decide

theorem residual_chunk_5_4_24 : initialChunk 5 4 24 = 254788627 := by
  decide

theorem residual_coeff_5_4_200 :
    (residualNumerator 5 4 200).natAbs = 61459280 := by
  decide

theorem residual_index_5_4_0 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (0 : Fin 8))) =
      (200 : Fin 293) := by
  decide

theorem residual_coeff_5_4_201 :
    (residualNumerator 5 4 201).natAbs = 22016772 := by
  decide

theorem residual_index_5_4_1 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (1 : Fin 8))) =
      (201 : Fin 293) := by
  decide

theorem residual_coeff_5_4_202 :
    (residualNumerator 5 4 202).natAbs = 83771842 := by
  decide

theorem residual_index_5_4_2 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (2 : Fin 8))) =
      (202 : Fin 293) := by
  decide

theorem residual_coeff_5_4_203 :
    (residualNumerator 5 4 203).natAbs = 4757865 := by
  decide

theorem residual_index_5_4_3 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (3 : Fin 8))) =
      (203 : Fin 293) := by
  decide

theorem residual_coeff_5_4_204 :
    (residualNumerator 5 4 204).natAbs = 16473931 := by
  decide

theorem residual_index_5_4_4 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (4 : Fin 8))) =
      (204 : Fin 293) := by
  decide

theorem residual_coeff_5_4_205 :
    (residualNumerator 5 4 205).natAbs = 10116278 := by
  decide

theorem residual_index_5_4_5 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (5 : Fin 8))) =
      (205 : Fin 293) := by
  decide

theorem residual_coeff_5_4_206 :
    (residualNumerator 5 4 206).natAbs = 17109384 := by
  decide

theorem residual_index_5_4_6 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (6 : Fin 8))) =
      (206 : Fin 293) := by
  decide

theorem residual_coeff_5_4_207 :
    (residualNumerator 5 4 207).natAbs = 16641483 := by
  decide

theorem residual_index_5_4_7 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (7 : Fin 8))) =
      (207 : Fin 293) := by
  decide

theorem residual_chunk_5_4_25 : initialChunk 5 4 25 = 232346835 := by
  unfold initialChunk
  rw [Fin.sum_univ_eight]
  rw [residual_index_5_4_0, residual_index_5_4_1, residual_index_5_4_2, residual_index_5_4_3, residual_index_5_4_4, residual_index_5_4_5, residual_index_5_4_6, residual_index_5_4_7]
  norm_num only [residual_coeff_5_4_200, residual_coeff_5_4_201, residual_coeff_5_4_202, residual_coeff_5_4_203, residual_coeff_5_4_204, residual_coeff_5_4_205, residual_coeff_5_4_206, residual_coeff_5_4_207]

theorem residual_chunk_5_4_26 : initialChunk 5 4 26 = 183632473 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_4_2 : initialPart 5 4 2 = 1707533280 := by
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
  rw [residual_chunk_5_4_18, residual_chunk_5_4_19, residual_chunk_5_4_20, residual_chunk_5_4_21, residual_chunk_5_4_22, residual_chunk_5_4_23, residual_chunk_5_4_24, residual_chunk_5_4_25, residual_chunk_5_4_26]

end LiteralP13HodgeCertificate
end GroupApproximation

