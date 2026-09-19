import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 18--26 for residual block (3, 2). -/

theorem residual_chunk_3_2_18 : initialChunk 3 2 18 = 130800208 := by
  decide

theorem residual_chunk_3_2_19 : initialChunk 3 2 19 = 148247475 := by
  decide

theorem residual_chunk_3_2_20 : initialChunk 3 2 20 = 216589654 := by
  decide

theorem residual_chunk_3_2_21 : initialChunk 3 2 21 = 176353614 := by
  decide

theorem residual_chunk_3_2_22 : initialChunk 3 2 22 = 441324403 := by
  decide

theorem residual_chunk_3_2_23 : initialChunk 3 2 23 = 193450939 := by
  decide

theorem residual_chunk_3_2_24 : initialChunk 3 2 24 = 279743322 := by
  decide

theorem residual_coeff_3_2_200 :
    (residualNumerator 3 2 200).natAbs = 122736390 := by
  decide

theorem residual_index_3_2_0 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (0 : Fin 8))) =
      (200 : Fin 293) := by
  decide

theorem residual_coeff_3_2_201 :
    (residualNumerator 3 2 201).natAbs = 132884849 := by
  decide

theorem residual_index_3_2_1 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (1 : Fin 8))) =
      (201 : Fin 293) := by
  decide

theorem residual_coeff_3_2_202 :
    (residualNumerator 3 2 202).natAbs = 40540963 := by
  decide

theorem residual_index_3_2_2 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (2 : Fin 8))) =
      (202 : Fin 293) := by
  decide

theorem residual_coeff_3_2_203 :
    (residualNumerator 3 2 203).natAbs = 22249753 := by
  decide

theorem residual_index_3_2_3 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (3 : Fin 8))) =
      (203 : Fin 293) := by
  decide

theorem residual_coeff_3_2_204 :
    (residualNumerator 3 2 204).natAbs = 2953261 := by
  decide

theorem residual_index_3_2_4 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (4 : Fin 8))) =
      (204 : Fin 293) := by
  decide

theorem residual_coeff_3_2_205 :
    (residualNumerator 3 2 205).natAbs = 39447970 := by
  decide

theorem residual_index_3_2_5 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (5 : Fin 8))) =
      (205 : Fin 293) := by
  decide

theorem residual_coeff_3_2_206 :
    (residualNumerator 3 2 206).natAbs = 24658430 := by
  decide

theorem residual_index_3_2_6 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (6 : Fin 8))) =
      (206 : Fin 293) := by
  decide

theorem residual_coeff_3_2_207 :
    (residualNumerator 3 2 207).natAbs = 3101956 := by
  decide

theorem residual_index_3_2_7 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (7 : Fin 8))) =
      (207 : Fin 293) := by
  decide

theorem residual_chunk_3_2_25 : initialChunk 3 2 25 = 388573572 := by
  unfold initialChunk
  rw [Fin.sum_univ_eight]
  rw [residual_index_3_2_0, residual_index_3_2_1, residual_index_3_2_2, residual_index_3_2_3, residual_index_3_2_4, residual_index_3_2_5, residual_index_3_2_6, residual_index_3_2_7]
  norm_num only [residual_coeff_3_2_200, residual_coeff_3_2_201, residual_coeff_3_2_202, residual_coeff_3_2_203, residual_coeff_3_2_204, residual_coeff_3_2_205, residual_coeff_3_2_206, residual_coeff_3_2_207]

theorem residual_chunk_3_2_26 : initialChunk 3 2 26 = 269061016 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_2_2 : initialPart 3 2 2 = 2244144203 := by
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
  rw [residual_chunk_3_2_18, residual_chunk_3_2_19, residual_chunk_3_2_20, residual_chunk_3_2_21, residual_chunk_3_2_22, residual_chunk_3_2_23, residual_chunk_3_2_24, residual_chunk_3_2_25, residual_chunk_3_2_26]

end LiteralP13HodgeCertificate
end GroupApproximation
