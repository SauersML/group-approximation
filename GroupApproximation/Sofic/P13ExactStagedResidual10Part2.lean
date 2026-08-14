import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 18--26 for residual block (1, 0). -/

theorem residual_chunk_1_0_18 : initialChunk 1 0 18 = 199570698 := by
  decide

theorem residual_chunk_1_0_19 : initialChunk 1 0 19 = 129633692 := by
  decide

theorem residual_chunk_1_0_20 : initialChunk 1 0 20 = 340264564 := by
  decide

theorem residual_chunk_1_0_21 : initialChunk 1 0 21 = 145910225 := by
  decide

theorem residual_chunk_1_0_22 : initialChunk 1 0 22 = 414361029 := by
  decide

theorem residual_chunk_1_0_23 : initialChunk 1 0 23 = 202245321 := by
  decide

theorem residual_chunk_1_0_24 : initialChunk 1 0 24 = 237656202 := by
  decide

theorem residual_coeff_1_0_200 :
    (residualNumerator 1 0 200).natAbs = 93574498 := by
  decide

theorem residual_index_1_0_0 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (0 : Fin 8))) =
      (200 : Fin 293) := by
  decide

theorem residual_coeff_1_0_201 :
    (residualNumerator 1 0 201).natAbs = 191278819 := by
  decide

theorem residual_index_1_0_1 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (1 : Fin 8))) =
      (201 : Fin 293) := by
  decide

theorem residual_coeff_1_0_202 :
    (residualNumerator 1 0 202).natAbs = 12896236 := by
  decide

theorem residual_index_1_0_2 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (2 : Fin 8))) =
      (202 : Fin 293) := by
  decide

theorem residual_coeff_1_0_203 :
    (residualNumerator 1 0 203).natAbs = 61277304 := by
  decide

theorem residual_index_1_0_3 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (3 : Fin 8))) =
      (203 : Fin 293) := by
  decide

theorem residual_coeff_1_0_204 :
    (residualNumerator 1 0 204).natAbs = 35454390 := by
  decide

theorem residual_index_1_0_4 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (4 : Fin 8))) =
      (204 : Fin 293) := by
  decide

theorem residual_coeff_1_0_205 :
    (residualNumerator 1 0 205).natAbs = 6040653 := by
  decide

theorem residual_index_1_0_5 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (5 : Fin 8))) =
      (205 : Fin 293) := by
  decide

theorem residual_coeff_1_0_206 :
    (residualNumerator 1 0 206).natAbs = 92453524 := by
  decide

theorem residual_index_1_0_6 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (6 : Fin 8))) =
      (206 : Fin 293) := by
  decide

theorem residual_coeff_1_0_207 :
    (residualNumerator 1 0 207).natAbs = 38030635 := by
  decide

theorem residual_index_1_0_7 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (7 : Fin 8))) =
      (207 : Fin 293) := by
  decide

theorem residual_chunk_1_0_25 : initialChunk 1 0 25 = 531006059 := by
  unfold initialChunk
  rw [Fin.sum_univ_eight]
  rw [residual_index_1_0_0, residual_index_1_0_1, residual_index_1_0_2, residual_index_1_0_3, residual_index_1_0_4, residual_index_1_0_5, residual_index_1_0_6, residual_index_1_0_7]
  norm_num only [residual_coeff_1_0_200, residual_coeff_1_0_201, residual_coeff_1_0_202, residual_coeff_1_0_203, residual_coeff_1_0_204, residual_coeff_1_0_205, residual_coeff_1_0_206, residual_coeff_1_0_207]

theorem residual_chunk_1_0_26 : initialChunk 1 0 26 = 159936432 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_0_2 : initialPart 1 0 2 = 2360584222 := by
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
  rw [residual_chunk_1_0_18, residual_chunk_1_0_19, residual_chunk_1_0_20, residual_chunk_1_0_21, residual_chunk_1_0_22, residual_chunk_1_0_23, residual_chunk_1_0_24, residual_chunk_1_0_25, residual_chunk_1_0_26]

end LiteralP13HodgeCertificate
end GroupApproximation

