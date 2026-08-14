import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 18--26 for residual block (5, 5). -/

theorem residual_chunk_5_5_18 : initialChunk 5 5 18 = 244766909 := by
  decide

theorem residual_chunk_5_5_19 : initialChunk 5 5 19 = 129487749 := by
  decide

theorem residual_chunk_5_5_20 : initialChunk 5 5 20 = 179170830 := by
  decide

theorem residual_chunk_5_5_21 : initialChunk 5 5 21 = 206475965 := by
  decide

theorem residual_chunk_5_5_22 : initialChunk 5 5 22 = 206058225 := by
  decide

theorem residual_chunk_5_5_23 : initialChunk 5 5 23 = 124403403 := by
  decide

theorem residual_chunk_5_5_24 : initialChunk 5 5 24 = 516161148 := by
  decide

theorem residual_coeff_5_5_200 :
    (residualNumerator 5 5 200).natAbs = 58583879 := by
  decide

theorem residual_index_5_5_0 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (0 : Fin 8))) =
      (200 : Fin 293) := by
  decide

theorem residual_coeff_5_5_201 :
    (residualNumerator 5 5 201).natAbs = 11615322578186 := by
  decide

theorem residual_index_5_5_1 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (1 : Fin 8))) =
      (201 : Fin 293) := by
  decide

theorem residual_coeff_5_5_202 :
    (residualNumerator 5 5 202).natAbs = 58583879 := by
  decide

theorem residual_index_5_5_2 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (2 : Fin 8))) =
      (202 : Fin 293) := by
  decide

theorem residual_coeff_5_5_203 :
    (residualNumerator 5 5 203).natAbs = 26699385 := by
  decide

theorem residual_index_5_5_3 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (3 : Fin 8))) =
      (203 : Fin 293) := by
  decide

theorem residual_coeff_5_5_204 :
    (residualNumerator 5 5 204).natAbs = 23761768 := by
  decide

theorem residual_index_5_5_4 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (4 : Fin 8))) =
      (204 : Fin 293) := by
  decide

theorem residual_coeff_5_5_205 :
    (residualNumerator 5 5 205).natAbs = 210405038 := by
  decide

theorem residual_index_5_5_5 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (5 : Fin 8))) =
      (205 : Fin 293) := by
  decide

theorem residual_coeff_5_5_206 :
    (residualNumerator 5 5 206).natAbs = 51590390 := by
  decide

theorem residual_index_5_5_6 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (6 : Fin 8))) =
      (206 : Fin 293) := by
  decide

theorem residual_coeff_5_5_207 :
    (residualNumerator 5 5 207).natAbs = 21760919 := by
  decide

theorem residual_index_5_5_7 :
    Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), (7 : Fin 8))) =
      (207 : Fin 293) := by
  decide

theorem residual_chunk_5_5_25 : initialChunk 5 5 25 = 11615773963444 := by
  unfold initialChunk
  rw [Fin.sum_univ_eight]
  rw [residual_index_5_5_0, residual_index_5_5_1, residual_index_5_5_2, residual_index_5_5_3, residual_index_5_5_4, residual_index_5_5_5, residual_index_5_5_6, residual_index_5_5_7]
  norm_num only [residual_coeff_5_5_200, residual_coeff_5_5_201, residual_coeff_5_5_202, residual_coeff_5_5_203, residual_coeff_5_5_204, residual_coeff_5_5_205, residual_coeff_5_5_206, residual_coeff_5_5_207]

theorem residual_chunk_5_5_26 : initialChunk 5 5 26 = 339214382 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_5_2 : initialPart 5 5 2 = 11617719702055 := by
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
  rw [residual_chunk_5_5_18, residual_chunk_5_5_19, residual_chunk_5_5_20, residual_chunk_5_5_21, residual_chunk_5_5_22, residual_chunk_5_5_23, residual_chunk_5_5_24, residual_chunk_5_5_25, residual_chunk_5_5_26]

end LiteralP13HodgeCertificate
end GroupApproximation

