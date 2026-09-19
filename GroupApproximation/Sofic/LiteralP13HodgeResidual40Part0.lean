import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (4, 0). -/

theorem residual_chunk_4_0_0 : initialChunk 4 0 0 = 94011494 := by
  decide

theorem residual_chunk_4_0_1 : initialChunk 4 0 1 = 221221077 := by
  decide

theorem residual_chunk_4_0_2 : initialChunk 4 0 2 = 162044750 := by
  decide

theorem residual_chunk_4_0_3 : initialChunk 4 0 3 = 478267011 := by
  decide

theorem residual_chunk_4_0_4 : initialChunk 4 0 4 = 209621209 := by
  decide

theorem residual_chunk_4_0_5 : initialChunk 4 0 5 = 305186638 := by
  decide

theorem residual_chunk_4_0_6 : initialChunk 4 0 6 = 329753054 := by
  decide

theorem residual_chunk_4_0_7 : initialChunk 4 0 7 = 189423129 := by
  decide

theorem residual_chunk_4_0_8 : initialChunk 4 0 8 = 293867973 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_0_0 : initialPart 4 0 0 = 2283396335 := by
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
  rw [residual_chunk_4_0_0, residual_chunk_4_0_1, residual_chunk_4_0_2, residual_chunk_4_0_3, residual_chunk_4_0_4, residual_chunk_4_0_5, residual_chunk_4_0_6, residual_chunk_4_0_7, residual_chunk_4_0_8]

end LiteralP13HodgeCertificate
end GroupApproximation
