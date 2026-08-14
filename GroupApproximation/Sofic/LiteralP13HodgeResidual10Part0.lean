import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (1, 0). -/

theorem residual_chunk_1_0_0 : initialChunk 1 0 0 = 172932567 := by
  decide

theorem residual_chunk_1_0_1 : initialChunk 1 0 1 = 218847908 := by
  decide

theorem residual_chunk_1_0_2 : initialChunk 1 0 2 = 341103463 := by
  decide

theorem residual_chunk_1_0_3 : initialChunk 1 0 3 = 335866090 := by
  decide

theorem residual_chunk_1_0_4 : initialChunk 1 0 4 = 157746328 := by
  decide

theorem residual_chunk_1_0_5 : initialChunk 1 0 5 = 256001192 := by
  decide

theorem residual_chunk_1_0_6 : initialChunk 1 0 6 = 236135925 := by
  decide

theorem residual_chunk_1_0_7 : initialChunk 1 0 7 = 205861253 := by
  decide

theorem residual_chunk_1_0_8 : initialChunk 1 0 8 = 377997777 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_0_0 : initialPart 1 0 0 = 2302492503 := by
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
  rw [residual_chunk_1_0_0, residual_chunk_1_0_1, residual_chunk_1_0_2, residual_chunk_1_0_3, residual_chunk_1_0_4, residual_chunk_1_0_5, residual_chunk_1_0_6, residual_chunk_1_0_7, residual_chunk_1_0_8]

end LiteralP13HodgeCertificate
end GroupApproximation
