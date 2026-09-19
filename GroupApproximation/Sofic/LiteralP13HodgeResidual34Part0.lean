import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (3, 4). -/

theorem residual_chunk_3_4_0 : initialChunk 3 4 0 = 123405856 := by
  decide

theorem residual_chunk_3_4_1 : initialChunk 3 4 1 = 183053215 := by
  decide

theorem residual_chunk_3_4_2 : initialChunk 3 4 2 = 163097200 := by
  decide

theorem residual_chunk_3_4_3 : initialChunk 3 4 3 = 204586640 := by
  decide

theorem residual_chunk_3_4_4 : initialChunk 3 4 4 = 121405858 := by
  decide

theorem residual_chunk_3_4_5 : initialChunk 3 4 5 = 71838264 := by
  decide

theorem residual_chunk_3_4_6 : initialChunk 3 4 6 = 139283688 := by
  decide

theorem residual_chunk_3_4_7 : initialChunk 3 4 7 = 90268886 := by
  decide

theorem residual_chunk_3_4_8 : initialChunk 3 4 8 = 70946796 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_4_0 : initialPart 3 4 0 = 1167886403 := by
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
  rw [residual_chunk_3_4_0, residual_chunk_3_4_1, residual_chunk_3_4_2, residual_chunk_3_4_3, residual_chunk_3_4_4, residual_chunk_3_4_5, residual_chunk_3_4_6, residual_chunk_3_4_7, residual_chunk_3_4_8]

end LiteralP13HodgeCertificate
end GroupApproximation
