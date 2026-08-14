import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--36 for residual block (1, 1). -/

theorem residual_chunk_1_1_27 : initialChunk 1 1 27 = 329191589 := by
  decide

theorem residual_chunk_1_1_28 : initialChunk 1 1 28 = 113208670 := by
  decide

theorem residual_chunk_1_1_29 : initialChunk 1 1 29 = 323366602 := by
  decide

theorem residual_chunk_1_1_30 : initialChunk 1 1 30 = 117066754 := by
  decide

theorem residual_chunk_1_1_31 : initialChunk 1 1 31 = 155874020 := by
  decide

theorem residual_chunk_1_1_32 : initialChunk 1 1 32 = 94572900 := by
  decide

theorem residual_chunk_1_1_33 : initialChunk 1 1 33 = 252219356 := by
  decide

theorem residual_chunk_1_1_34 : initialChunk 1 1 34 = 186769554 := by
  decide

theorem residual_chunk_1_1_35 : initialChunk 1 1 35 = 186750138 := by
  decide

theorem residual_chunk_1_1_36 : finalChunk 1 1 = 59825574 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_1_3 : initialPart 1 1 3 + finalChunk 1 1 = 1818845157 := by
  unfold initialPart
  rw [sum_fin9_explicit]
  rw [show finProdFinEquiv ((3 : Fin 4), (0 : Fin 9)) = (27 : Fin 36) by decide]
  rw [show finProdFinEquiv ((3 : Fin 4), (1 : Fin 9)) = (28 : Fin 36) by decide]
  rw [show finProdFinEquiv ((3 : Fin 4), (2 : Fin 9)) = (29 : Fin 36) by decide]
  rw [show finProdFinEquiv ((3 : Fin 4), (3 : Fin 9)) = (30 : Fin 36) by decide]
  rw [show finProdFinEquiv ((3 : Fin 4), (4 : Fin 9)) = (31 : Fin 36) by decide]
  rw [show finProdFinEquiv ((3 : Fin 4), (5 : Fin 9)) = (32 : Fin 36) by decide]
  rw [show finProdFinEquiv ((3 : Fin 4), (6 : Fin 9)) = (33 : Fin 36) by decide]
  rw [show finProdFinEquiv ((3 : Fin 4), (7 : Fin 9)) = (34 : Fin 36) by decide]
  rw [show finProdFinEquiv ((3 : Fin 4), (8 : Fin 9)) = (35 : Fin 36) by decide]
  rw [residual_chunk_1_1_27, residual_chunk_1_1_28, residual_chunk_1_1_29, residual_chunk_1_1_30, residual_chunk_1_1_31, residual_chunk_1_1_32, residual_chunk_1_1_33, residual_chunk_1_1_34, residual_chunk_1_1_35, residual_chunk_1_1_36]

end LiteralP13HodgeCertificate
end GroupApproximation

