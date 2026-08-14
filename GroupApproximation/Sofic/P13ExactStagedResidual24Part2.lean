import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 18--26 for residual block (2, 4). -/

theorem residual_chunk_2_4_18 : initialChunk 2 4 18 = 216403351 := by
  decide

theorem residual_chunk_2_4_19 : initialChunk 2 4 19 = 141445519 := by
  decide

theorem residual_chunk_2_4_20 : initialChunk 2 4 20 = 178892672 := by
  decide

theorem residual_chunk_2_4_21 : initialChunk 2 4 21 = 77917132 := by
  decide

theorem residual_chunk_2_4_22 : initialChunk 2 4 22 = 200155851 := by
  decide

theorem residual_chunk_2_4_23 : initialChunk 2 4 23 = 250964576 := by
  decide

theorem residual_chunk_2_4_24 : initialChunk 2 4 24 = 318306143 := by
  decide

theorem residual_coeff_2_4_200 :
    (residualNumerator 2 4 200).natAbs = 31291770 := by
  decide

theorem residual_index_2_4_0 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (0 : Fin 8))) =
      (200 : Fin 293) := by
  decide

theorem residual_coeff_2_4_201 :
    (residualNumerator 2 4 201).natAbs = 97409680 := by
  decide

theorem residual_index_2_4_1 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (1 : Fin 8))) =
      (201 : Fin 293) := by
  decide

theorem residual_coeff_2_4_202 :
    (residualNumerator 2 4 202).natAbs = 48285482 := by
  decide

theorem residual_index_2_4_2 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (2 : Fin 8))) =
      (202 : Fin 293) := by
  decide

theorem residual_coeff_2_4_203 :
    (residualNumerator 2 4 203).natAbs = 31112689 := by
  decide

theorem residual_index_2_4_3 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (3 : Fin 8))) =
      (203 : Fin 293) := by
  decide

theorem residual_coeff_2_4_204 :
    (residualNumerator 2 4 204).natAbs = 13897149 := by
  decide

theorem residual_index_2_4_4 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (4 : Fin 8))) =
      (204 : Fin 293) := by
  decide

theorem residual_coeff_2_4_205 :
    (residualNumerator 2 4 205).natAbs = 49895325 := by
  decide

theorem residual_index_2_4_5 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (5 : Fin 8))) =
      (205 : Fin 293) := by
  decide

theorem residual_coeff_2_4_206 :
    (residualNumerator 2 4 206).natAbs = 5336337 := by
  decide

theorem residual_index_2_4_6 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (6 : Fin 8))) =
      (206 : Fin 293) := by
  decide

theorem residual_coeff_2_4_207 :
    (residualNumerator 2 4 207).natAbs = 3791249 := by
  decide

theorem residual_index_2_4_7 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (7 : Fin 8))) =
      (207 : Fin 293) := by
  decide

theorem residual_chunk_2_4_25 : initialChunk 2 4 25 = 281019681 := by
  unfold initialChunk
  rw [Fin.sum_univ_eight]
  rw [residual_index_2_4_0, residual_index_2_4_1, residual_index_2_4_2, residual_index_2_4_3, residual_index_2_4_4, residual_index_2_4_5, residual_index_2_4_6, residual_index_2_4_7]
  norm_num only [residual_coeff_2_4_200, residual_coeff_2_4_201, residual_coeff_2_4_202, residual_coeff_2_4_203, residual_coeff_2_4_204, residual_coeff_2_4_205, residual_coeff_2_4_206, residual_coeff_2_4_207]

theorem residual_chunk_2_4_26 : initialChunk 2 4 26 = 246298101 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_4_2 : initialPart 2 4 2 = 1911403026 := by
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
  rw [residual_chunk_2_4_18, residual_chunk_2_4_19, residual_chunk_2_4_20, residual_chunk_2_4_21, residual_chunk_2_4_22, residual_chunk_2_4_23, residual_chunk_2_4_24, residual_chunk_2_4_25, residual_chunk_2_4_26]

end LiteralP13HodgeCertificate
end GroupApproximation

