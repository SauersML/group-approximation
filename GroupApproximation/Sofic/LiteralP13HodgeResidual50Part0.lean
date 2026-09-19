import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (5, 0). -/

theorem residual_chunk_5_0_0 : initialChunk 5 0 0 = 160579150 := by
  decide

theorem residual_chunk_5_0_1 : initialChunk 5 0 1 = 198726187 := by
  decide

theorem residual_chunk_5_0_2 : initialChunk 5 0 2 = 88175333 := by
  decide

theorem residual_chunk_5_0_3 : initialChunk 5 0 3 = 407500692 := by
  decide

theorem residual_chunk_5_0_4 : initialChunk 5 0 4 = 121099381 := by
  decide

theorem residual_chunk_5_0_5 : initialChunk 5 0 5 = 238240901 := by
  decide

theorem residual_chunk_5_0_6 : initialChunk 5 0 6 = 297684492 := by
  decide

theorem residual_chunk_5_0_7 : initialChunk 5 0 7 = 217469228 := by
  decide

theorem residual_chunk_5_0_8 : initialChunk 5 0 8 = 279200632 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_0_0 : initialPart 5 0 0 = 2008675996 := by
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
  rw [residual_chunk_5_0_0, residual_chunk_5_0_1, residual_chunk_5_0_2, residual_chunk_5_0_3, residual_chunk_5_0_4, residual_chunk_5_0_5, residual_chunk_5_0_6, residual_chunk_5_0_7, residual_chunk_5_0_8]

end LiteralP13HodgeCertificate
end GroupApproximation
