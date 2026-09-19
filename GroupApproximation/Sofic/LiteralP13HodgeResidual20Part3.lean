import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--35 for residual block (2, 0). -/

theorem residual_chunk_2_0_27 : initialChunk 2 0 27 = 330718522 := by
  decide

theorem residual_chunk_2_0_28 : initialChunk 2 0 28 = 87624428 := by
  decide

theorem residual_chunk_2_0_29 : initialChunk 2 0 29 = 434787992 := by
  decide

theorem residual_chunk_2_0_30 : initialChunk 2 0 30 = 205667556 := by
  decide

theorem residual_chunk_2_0_31 : initialChunk 2 0 31 = 216885695 := by
  decide

theorem residual_chunk_2_0_32 : initialChunk 2 0 32 = 206808233 := by
  decide

theorem residual_chunk_2_0_33 : initialChunk 2 0 33 = 321866086 := by
  decide

theorem residual_chunk_2_0_34 : initialChunk 2 0 34 = 93554551 := by
  decide

theorem residual_chunk_2_0_35 : initialChunk 2 0 35 = 157730458 := by
  decide

theorem residual_chunk_2_0_36 : finalChunk 2 0 = 92083950 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_0_3 : initialPart 2 0 3 + finalChunk 2 0 = 2147727471 := by
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
  rw [residual_chunk_2_0_27, residual_chunk_2_0_28, residual_chunk_2_0_29, residual_chunk_2_0_30, residual_chunk_2_0_31, residual_chunk_2_0_32, residual_chunk_2_0_33, residual_chunk_2_0_34, residual_chunk_2_0_35, residual_chunk_2_0_36]

end LiteralP13HodgeCertificate
end GroupApproximation
