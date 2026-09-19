import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 18--26 for residual block (1, 1). -/

theorem residual_chunk_1_1_18 : initialChunk 1 1 18 = 159558275 := by
  decide

theorem residual_chunk_1_1_19 : initialChunk 1 1 19 = 164289773 := by
  decide

theorem residual_chunk_1_1_20 : initialChunk 1 1 20 = 521937435 := by
  decide

theorem residual_chunk_1_1_21 : initialChunk 1 1 21 = 139737742 := by
  decide

theorem residual_chunk_1_1_22 : initialChunk 1 1 22 = 173892675 := by
  decide

theorem residual_chunk_1_1_23 : initialChunk 1 1 23 = 219130764 := by
  decide

theorem residual_chunk_1_1_24 : initialChunk 1 1 24 = 200856101 := by
  decide

theorem residual_coeff_1_1_200 :
    (residualNumerator 1 1 200).natAbs = 90659415 := by
  decide

theorem residual_index_1_1_0 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (0 : Fin 8))) =
      (200 : Fin 293) := by
  decide

theorem residual_coeff_1_1_201 :
    (residualNumerator 1 1 201).natAbs = 11615556300504 := by
  decide

theorem residual_index_1_1_1 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (1 : Fin 8))) =
      (201 : Fin 293) := by
  decide

theorem residual_coeff_1_1_202 :
    (residualNumerator 1 1 202).natAbs = 90659415 := by
  decide

theorem residual_index_1_1_2 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (2 : Fin 8))) =
      (202 : Fin 293) := by
  decide

theorem residual_coeff_1_1_203 :
    (residualNumerator 1 1 203).natAbs = 5683622 := by
  decide

theorem residual_index_1_1_3 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (3 : Fin 8))) =
      (203 : Fin 293) := by
  decide

theorem residual_coeff_1_1_204 :
    (residualNumerator 1 1 204).natAbs = 7964634 := by
  decide

theorem residual_index_1_1_4 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (4 : Fin 8))) =
      (204 : Fin 293) := by
  decide

theorem residual_coeff_1_1_205 :
    (residualNumerator 1 1 205).natAbs = 93238345 := by
  decide

theorem residual_index_1_1_5 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (5 : Fin 8))) =
      (205 : Fin 293) := by
  decide

theorem residual_coeff_1_1_206 :
    (residualNumerator 1 1 206).natAbs = 14438254 := by
  decide

theorem residual_index_1_1_6 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (6 : Fin 8))) =
      (206 : Fin 293) := by
  decide

theorem residual_coeff_1_1_207 :
    (residualNumerator 1 1 207).natAbs = 223685 := by
  decide

theorem residual_index_1_1_7 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (7 : Fin 8))) =
      (207 : Fin 293) := by
  decide

theorem residual_chunk_1_1_25 : initialChunk 1 1 25 = 11615859167874 := by
  unfold initialChunk
  rw [Fin.sum_univ_eight]
  rw [residual_index_1_1_0, residual_index_1_1_1, residual_index_1_1_2, residual_index_1_1_3, residual_index_1_1_4, residual_index_1_1_5, residual_index_1_1_6, residual_index_1_1_7]
  norm_num only [residual_coeff_1_1_200, residual_coeff_1_1_201, residual_coeff_1_1_202, residual_coeff_1_1_203, residual_coeff_1_1_204, residual_coeff_1_1_205, residual_coeff_1_1_206, residual_coeff_1_1_207]

theorem residual_chunk_1_1_26 : initialChunk 1 1 26 = 280576683 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_1_2 : initialPart 1 1 2 = 11617719147322 := by
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
  rw [residual_chunk_1_1_18, residual_chunk_1_1_19, residual_chunk_1_1_20, residual_chunk_1_1_21, residual_chunk_1_1_22, residual_chunk_1_1_23, residual_chunk_1_1_24, residual_chunk_1_1_25, residual_chunk_1_1_26]

end LiteralP13HodgeCertificate
end GroupApproximation
