import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 18--26 for residual block (1, 4). -/

theorem residual_chunk_1_4_18 : initialChunk 1 4 18 = 262741310 := by
  decide

theorem residual_chunk_1_4_19 : initialChunk 1 4 19 = 52506302 := by
  decide

theorem residual_chunk_1_4_20 : initialChunk 1 4 20 = 179942748 := by
  decide

theorem residual_chunk_1_4_21 : initialChunk 1 4 21 = 114219620 := by
  decide

theorem residual_chunk_1_4_22 : initialChunk 1 4 22 = 242990175 := by
  decide

theorem residual_chunk_1_4_23 : initialChunk 1 4 23 = 181054224 := by
  decide

theorem residual_chunk_1_4_24 : initialChunk 1 4 24 = 78073303 := by
  decide

theorem residual_coeff_1_4_200 :
    (residualNumerator 1 4 200).natAbs = 28362123 := by
  decide

theorem residual_index_1_4_0 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (0 : Fin 8))) =
      (200 : Fin 293) := by
  decide

theorem residual_coeff_1_4_201 :
    (residualNumerator 1 4 201).natAbs = 102223018 := by
  decide

theorem residual_index_1_4_1 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (1 : Fin 8))) =
      (201 : Fin 293) := by
  decide

theorem residual_coeff_1_4_202 :
    (residualNumerator 1 4 202).natAbs = 45081335 := by
  decide

theorem residual_index_1_4_2 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (2 : Fin 8))) =
      (202 : Fin 293) := by
  decide

theorem residual_coeff_1_4_203 :
    (residualNumerator 1 4 203).natAbs = 25140210 := by
  decide

theorem residual_index_1_4_3 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (3 : Fin 8))) =
      (203 : Fin 293) := by
  decide

theorem residual_coeff_1_4_204 :
    (residualNumerator 1 4 204).natAbs = 1244154 := by
  decide

theorem residual_index_1_4_4 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (4 : Fin 8))) =
      (204 : Fin 293) := by
  decide

theorem residual_coeff_1_4_205 :
    (residualNumerator 1 4 205).natAbs = 70789655 := by
  decide

theorem residual_index_1_4_5 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (5 : Fin 8))) =
      (205 : Fin 293) := by
  decide

theorem residual_coeff_1_4_206 :
    (residualNumerator 1 4 206).natAbs = 25045128 := by
  decide

theorem residual_index_1_4_6 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (6 : Fin 8))) =
      (206 : Fin 293) := by
  decide

theorem residual_coeff_1_4_207 :
    (residualNumerator 1 4 207).natAbs = 5480889 := by
  decide

theorem residual_index_1_4_7 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (7 : Fin 8))) =
      (207 : Fin 293) := by
  decide

theorem residual_chunk_1_4_25 : initialChunk 1 4 25 = 303366512 := by
  unfold initialChunk
  rw [Fin.sum_univ_eight]
  rw [residual_index_1_4_0, residual_index_1_4_1, residual_index_1_4_2, residual_index_1_4_3, residual_index_1_4_4, residual_index_1_4_5, residual_index_1_4_6, residual_index_1_4_7]
  norm_num only [residual_coeff_1_4_200, residual_coeff_1_4_201, residual_coeff_1_4_202, residual_coeff_1_4_203, residual_coeff_1_4_204, residual_coeff_1_4_205, residual_coeff_1_4_206, residual_coeff_1_4_207]

theorem residual_chunk_1_4_26 : initialChunk 1 4 26 = 290866946 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_4_2 : initialPart 1 4 2 = 1705761140 := by
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
  rw [residual_chunk_1_4_18, residual_chunk_1_4_19, residual_chunk_1_4_20, residual_chunk_1_4_21, residual_chunk_1_4_22, residual_chunk_1_4_23, residual_chunk_1_4_24, residual_chunk_1_4_25, residual_chunk_1_4_26]

end LiteralP13HodgeCertificate
end GroupApproximation
