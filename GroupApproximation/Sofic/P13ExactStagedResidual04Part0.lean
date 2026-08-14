import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (0, 4). -/

theorem residual_chunk_0_4_0 : initialChunk 0 4 0 = 380345788 := by
  decide

theorem residual_chunk_0_4_1 : initialChunk 0 4 1 = 271428555 := by
  decide

theorem residual_chunk_0_4_2 : initialChunk 0 4 2 = 344697023 := by
  decide

theorem residual_chunk_0_4_3 : initialChunk 0 4 3 = 396327188 := by
  decide

theorem residual_chunk_0_4_4 : initialChunk 0 4 4 = 179872728 := by
  decide

theorem residual_chunk_0_4_5 : initialChunk 0 4 5 = 289520479 := by
  decide

theorem residual_chunk_0_4_6 : initialChunk 0 4 6 = 171207824 := by
  decide

theorem residual_chunk_0_4_7 : initialChunk 0 4 7 = 200215315 := by
  decide

theorem residual_chunk_0_4_8 : initialChunk 0 4 8 = 112387375 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_4_0 : initialPart 0 4 0 = 2346002275 := by
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
  rw [residual_chunk_0_4_0, residual_chunk_0_4_1, residual_chunk_0_4_2, residual_chunk_0_4_3, residual_chunk_0_4_4, residual_chunk_0_4_5, residual_chunk_0_4_6, residual_chunk_0_4_7, residual_chunk_0_4_8]

end LiteralP13HodgeCertificate
end GroupApproximation

