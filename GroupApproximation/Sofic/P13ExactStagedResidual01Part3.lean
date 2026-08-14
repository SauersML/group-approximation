import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--36 for residual block (0, 1). -/

theorem residual_chunk_0_1_27 : initialChunk 0 1 27 = 390549844 := by
  decide

theorem residual_chunk_0_1_28 : initialChunk 0 1 28 = 165642307 := by
  decide

theorem residual_chunk_0_1_29 : initialChunk 0 1 29 = 183630920 := by
  decide

theorem residual_chunk_0_1_30 : initialChunk 0 1 30 = 256970346 := by
  decide

theorem residual_chunk_0_1_31 : initialChunk 0 1 31 = 229632481 := by
  decide

theorem residual_chunk_0_1_32 : initialChunk 0 1 32 = 116430027 := by
  decide

theorem residual_chunk_0_1_33 : initialChunk 0 1 33 = 478577056 := by
  decide

theorem residual_chunk_0_1_34 : initialChunk 0 1 34 = 168986936 := by
  decide

theorem residual_chunk_0_1_35 : initialChunk 0 1 35 = 181139148 := by
  decide

theorem residual_chunk_0_1_36 : finalChunk 0 1 = 125880049 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_1_3 : initialPart 0 1 3 + finalChunk 0 1 = 2297439114 := by
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
  rw [residual_chunk_0_1_27, residual_chunk_0_1_28, residual_chunk_0_1_29, residual_chunk_0_1_30, residual_chunk_0_1_31, residual_chunk_0_1_32, residual_chunk_0_1_33, residual_chunk_0_1_34, residual_chunk_0_1_35, residual_chunk_0_1_36]

end LiteralP13HodgeCertificate
end GroupApproximation

