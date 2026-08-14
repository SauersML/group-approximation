import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--35 for residual block (0, 2). -/

theorem residual_chunk_0_2_27 : initialChunk 0 2 27 = 323676915 := by
  decide

theorem residual_chunk_0_2_28 : initialChunk 0 2 28 = 174434929 := by
  decide

theorem residual_chunk_0_2_29 : initialChunk 0 2 29 = 300929297 := by
  decide

theorem residual_chunk_0_2_30 : initialChunk 0 2 30 = 180466118 := by
  decide

theorem residual_chunk_0_2_31 : initialChunk 0 2 31 = 164795238 := by
  decide

theorem residual_chunk_0_2_32 : initialChunk 0 2 32 = 86817189 := by
  decide

theorem residual_chunk_0_2_33 : initialChunk 0 2 33 = 355379563 := by
  decide

theorem residual_chunk_0_2_34 : initialChunk 0 2 34 = 143131266 := by
  decide

theorem residual_chunk_0_2_35 : initialChunk 0 2 35 = 271695724 := by
  decide

theorem residual_chunk_0_2_36 : finalChunk 0 2 = 172733798 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_2_3 : initialPart 0 2 3 + finalChunk 0 2 = 2174060037 := by
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
  rw [residual_chunk_0_2_27, residual_chunk_0_2_28, residual_chunk_0_2_29, residual_chunk_0_2_30, residual_chunk_0_2_31, residual_chunk_0_2_32, residual_chunk_0_2_33, residual_chunk_0_2_34, residual_chunk_0_2_35, residual_chunk_0_2_36]

end LiteralP13HodgeCertificate
end GroupApproximation
