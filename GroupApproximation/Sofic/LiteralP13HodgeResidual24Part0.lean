import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (2, 4). -/

theorem residual_chunk_2_4_0 : initialChunk 2 4 0 = 401428553 := by
  decide

theorem residual_chunk_2_4_1 : initialChunk 2 4 1 = 326754301 := by
  decide

theorem residual_chunk_2_4_2 : initialChunk 2 4 2 = 240151434 := by
  decide

theorem residual_chunk_2_4_3 : initialChunk 2 4 3 = 214481363 := by
  decide

theorem residual_chunk_2_4_4 : initialChunk 2 4 4 = 184287535 := by
  decide

theorem residual_chunk_2_4_5 : initialChunk 2 4 5 = 367957766 := by
  decide

theorem residual_chunk_2_4_6 : initialChunk 2 4 6 = 180994628 := by
  decide

theorem residual_chunk_2_4_7 : initialChunk 2 4 7 = 133782050 := by
  decide

theorem residual_chunk_2_4_8 : initialChunk 2 4 8 = 128161147 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_4_0 : initialPart 2 4 0 = 2177998777 := by
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
  rw [residual_chunk_2_4_0, residual_chunk_2_4_1, residual_chunk_2_4_2, residual_chunk_2_4_3, residual_chunk_2_4_4, residual_chunk_2_4_5, residual_chunk_2_4_6, residual_chunk_2_4_7, residual_chunk_2_4_8]

end LiteralP13HodgeCertificate
end GroupApproximation
