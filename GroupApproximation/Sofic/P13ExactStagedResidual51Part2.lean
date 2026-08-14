import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 18--26 for residual block (5, 1). -/

theorem residual_chunk_5_1_18 : initialChunk 5 1 18 = 192611864 := by
  decide

theorem residual_chunk_5_1_19 : initialChunk 5 1 19 = 206237866 := by
  decide

theorem residual_chunk_5_1_20 : initialChunk 5 1 20 = 317900892 := by
  decide

theorem residual_chunk_5_1_21 : initialChunk 5 1 21 = 162078738 := by
  decide

theorem residual_chunk_5_1_22 : initialChunk 5 1 22 = 110390265 := by
  decide

theorem residual_chunk_5_1_23 : initialChunk 5 1 23 = 123213386 := by
  decide

theorem residual_chunk_5_1_24 : initialChunk 5 1 24 = 284871521 := by
  decide

theorem residual_coeff_5_1_200 :
    (residualNumerator 5 1 200).natAbs = 151687450 := by
  decide

theorem residual_index_5_1_0 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (0 : Fin 8))) =
      (200 : Fin 293) := by
  decide

theorem residual_coeff_5_1_201 :
    (residualNumerator 5 1 201).natAbs = 195588232 := by
  decide

theorem residual_index_5_1_1 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (1 : Fin 8))) =
      (201 : Fin 293) := by
  decide

theorem residual_coeff_5_1_202 :
    (residualNumerator 5 1 202).natAbs = 27172063 := by
  decide

theorem residual_index_5_1_2 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (2 : Fin 8))) =
      (202 : Fin 293) := by
  decide

theorem residual_coeff_5_1_203 :
    (residualNumerator 5 1 203).natAbs = 23922063 := by
  decide

theorem residual_index_5_1_3 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (3 : Fin 8))) =
      (203 : Fin 293) := by
  decide

theorem residual_coeff_5_1_204 :
    (residualNumerator 5 1 204).natAbs = 9568542 := by
  decide

theorem residual_index_5_1_4 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (4 : Fin 8))) =
      (204 : Fin 293) := by
  decide

theorem residual_coeff_5_1_205 :
    (residualNumerator 5 1 205).natAbs = 92339633 := by
  decide

theorem residual_index_5_1_5 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (5 : Fin 8))) =
      (205 : Fin 293) := by
  decide

theorem residual_coeff_5_1_206 :
    (residualNumerator 5 1 206).natAbs = 6618793 := by
  decide

theorem residual_index_5_1_6 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (6 : Fin 8))) =
      (206 : Fin 293) := by
  decide

theorem residual_coeff_5_1_207 :
    (residualNumerator 5 1 207).natAbs = 9801253 := by
  decide

theorem residual_index_5_1_7 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (7 : Fin 8))) =
      (207 : Fin 293) := by
  decide

theorem residual_chunk_5_1_25 : initialChunk 5 1 25 = 516698029 := by
  unfold initialChunk
  rw [Fin.sum_univ_eight]
  rw [residual_index_5_1_0, residual_index_5_1_1, residual_index_5_1_2, residual_index_5_1_3, residual_index_5_1_4, residual_index_5_1_5, residual_index_5_1_6, residual_index_5_1_7]
  norm_num only [residual_coeff_5_1_200, residual_coeff_5_1_201, residual_coeff_5_1_202, residual_coeff_5_1_203, residual_coeff_5_1_204, residual_coeff_5_1_205, residual_coeff_5_1_206, residual_coeff_5_1_207]

theorem residual_chunk_5_1_26 : initialChunk 5 1 26 = 188448922 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_1_2 : initialPart 5 1 2 = 2102451483 := by
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
  rw [residual_chunk_5_1_18, residual_chunk_5_1_19, residual_chunk_5_1_20, residual_chunk_5_1_21, residual_chunk_5_1_22, residual_chunk_5_1_23, residual_chunk_5_1_24, residual_chunk_5_1_25, residual_chunk_5_1_26]

end LiteralP13HodgeCertificate
end GroupApproximation

