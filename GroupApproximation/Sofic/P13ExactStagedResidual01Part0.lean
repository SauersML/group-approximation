import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (0, 1). -/

theorem residual_chunk_0_1_0 : initialChunk 0 1 0 = 253347738 := by
  decide

theorem residual_chunk_0_1_1 : initialChunk 0 1 1 = 246756247 := by
  decide

theorem residual_chunk_0_1_2 : initialChunk 0 1 2 = 442291540 := by
  decide

theorem residual_chunk_0_1_3 : initialChunk 0 1 3 = 331021206 := by
  decide

theorem residual_chunk_0_1_4 : initialChunk 0 1 4 = 297443486 := by
  decide

theorem residual_chunk_0_1_5 : initialChunk 0 1 5 = 363492475 := by
  decide

theorem residual_chunk_0_1_6 : initialChunk 0 1 6 = 142837137 := by
  decide

theorem residual_chunk_0_1_7 : initialChunk 0 1 7 = 189109489 := by
  decide

theorem residual_chunk_0_1_8 : initialChunk 0 1 8 = 84924691 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_1_0 : initialPart 0 1 0 = 2351224009 := by
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
  rw [residual_chunk_0_1_0, residual_chunk_0_1_1, residual_chunk_0_1_2, residual_chunk_0_1_3, residual_chunk_0_1_4, residual_chunk_0_1_5, residual_chunk_0_1_6, residual_chunk_0_1_7, residual_chunk_0_1_8]

end LiteralP13HodgeCertificate
end GroupApproximation

