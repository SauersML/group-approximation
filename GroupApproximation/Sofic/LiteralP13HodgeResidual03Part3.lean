import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--35 for residual block (0, 3). -/

theorem residual_chunk_0_3_27 : initialChunk 0 3 27 = 487999772 := by
  decide

theorem residual_chunk_0_3_28 : initialChunk 0 3 28 = 174874196 := by
  decide

theorem residual_chunk_0_3_29 : initialChunk 0 3 29 = 209933059 := by
  decide

theorem residual_chunk_0_3_30 : initialChunk 0 3 30 = 346647985 := by
  decide

theorem residual_chunk_0_3_31 : initialChunk 0 3 31 = 191402474 := by
  decide

theorem residual_chunk_0_3_32 : initialChunk 0 3 32 = 172174706 := by
  decide

theorem residual_chunk_0_3_33 : initialChunk 0 3 33 = 673593690 := by
  decide

theorem residual_chunk_0_3_34 : initialChunk 0 3 34 = 216200136 := by
  decide

theorem residual_chunk_0_3_35 : initialChunk 0 3 35 = 279193183 := by
  decide

theorem residual_chunk_0_3_36 : finalChunk 0 3 = 258917352 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_3_3 : initialPart 0 3 3 + finalChunk 0 3 = 3010936553 := by
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
  rw [residual_chunk_0_3_27, residual_chunk_0_3_28, residual_chunk_0_3_29, residual_chunk_0_3_30, residual_chunk_0_3_31, residual_chunk_0_3_32, residual_chunk_0_3_33, residual_chunk_0_3_34, residual_chunk_0_3_35, residual_chunk_0_3_36]

end LiteralP13HodgeCertificate
end GroupApproximation
