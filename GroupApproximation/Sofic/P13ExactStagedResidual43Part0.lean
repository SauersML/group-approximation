import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (4, 3). -/

theorem residual_chunk_4_3_0 : initialChunk 4 3 0 = 116472011 := by
  decide

theorem residual_chunk_4_3_1 : initialChunk 4 3 1 = 63218168 := by
  decide

theorem residual_chunk_4_3_2 : initialChunk 4 3 2 = 156315025 := by
  decide

theorem residual_chunk_4_3_3 : initialChunk 4 3 3 = 227384172 := by
  decide

theorem residual_chunk_4_3_4 : initialChunk 4 3 4 = 100159394 := by
  decide

theorem residual_chunk_4_3_5 : initialChunk 4 3 5 = 84746997 := by
  decide

theorem residual_chunk_4_3_6 : initialChunk 4 3 6 = 194929469 := by
  decide

theorem residual_chunk_4_3_7 : initialChunk 4 3 7 = 85998634 := by
  decide

theorem residual_chunk_4_3_8 : initialChunk 4 3 8 = 135593277 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_3_0 : initialPart 4 3 0 = 1164817147 := by
  unfold initialPart
  rw [sum_fin9_explicit]
  rw [show finProdFinEquiv ((0 : Fin 4), (0 : Fin 9)) = (0 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (1 : Fin 9)) = (1 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (2 : Fin 9)) = (2 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (3 : Fin 9)) = (3 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (4 : Fin 9)) = (4 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (5 : Fin 9)) = (5 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (6 : Fin 9)) = (6 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (7 : Fin 9)) = (7 : Fin 36) by decide]
  rw [show finProdFinEquiv ((0 : Fin 4), (8 : Fin 9)) = (8 : Fin 36) by decide]
  rw [residual_chunk_4_3_0, residual_chunk_4_3_1, residual_chunk_4_3_2, residual_chunk_4_3_3, residual_chunk_4_3_4, residual_chunk_4_3_5, residual_chunk_4_3_6, residual_chunk_4_3_7, residual_chunk_4_3_8]

end LiteralP13HodgeCertificate
end GroupApproximation

