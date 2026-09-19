import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--35 for residual block (5, 3). -/

theorem residual_chunk_5_3_27 : initialChunk 5 3 27 = 208738827 := by
  decide

theorem residual_chunk_5_3_28 : initialChunk 5 3 28 = 190079109 := by
  decide

theorem residual_chunk_5_3_29 : initialChunk 5 3 29 = 227890374 := by
  decide

theorem residual_chunk_5_3_30 : initialChunk 5 3 30 = 238211282 := by
  decide

theorem residual_chunk_5_3_31 : initialChunk 5 3 31 = 138177071 := by
  decide

theorem residual_chunk_5_3_32 : initialChunk 5 3 32 = 158505476 := by
  decide

theorem residual_chunk_5_3_33 : initialChunk 5 3 33 = 224093264 := by
  decide

theorem residual_chunk_5_3_34 : initialChunk 5 3 34 = 77257752 := by
  decide

theorem residual_chunk_5_3_35 : initialChunk 5 3 35 = 172536888 := by
  decide

theorem residual_chunk_5_3_36 : finalChunk 5 3 = 111795580 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_3_3 : initialPart 5 3 3 + finalChunk 5 3 = 1747285623 := by
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
  rw [residual_chunk_5_3_27, residual_chunk_5_3_28, residual_chunk_5_3_29, residual_chunk_5_3_30, residual_chunk_5_3_31, residual_chunk_5_3_32, residual_chunk_5_3_33, residual_chunk_5_3_34, residual_chunk_5_3_35, residual_chunk_5_3_36]

end LiteralP13HodgeCertificate
end GroupApproximation
