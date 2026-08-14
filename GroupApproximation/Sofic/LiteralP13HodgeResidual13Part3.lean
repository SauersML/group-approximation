import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--35 for residual block (1, 3). -/

theorem residual_chunk_1_3_27 : initialChunk 1 3 27 = 150019880 := by
  decide

theorem residual_chunk_1_3_28 : initialChunk 1 3 28 = 151222173 := by
  decide

theorem residual_chunk_1_3_29 : initialChunk 1 3 29 = 302188503 := by
  decide

theorem residual_chunk_1_3_30 : initialChunk 1 3 30 = 97102388 := by
  decide

theorem residual_chunk_1_3_31 : initialChunk 1 3 31 = 202118589 := by
  decide

theorem residual_chunk_1_3_32 : initialChunk 1 3 32 = 211209311 := by
  decide

theorem residual_chunk_1_3_33 : initialChunk 1 3 33 = 274770193 := by
  decide

theorem residual_chunk_1_3_34 : initialChunk 1 3 34 = 63898215 := by
  decide

theorem residual_chunk_1_3_35 : initialChunk 1 3 35 = 111909964 := by
  decide

theorem residual_chunk_1_3_36 : finalChunk 1 3 = 91811235 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_3_3 : initialPart 1 3 3 + finalChunk 1 3 = 1656250451 := by
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
  rw [residual_chunk_1_3_27, residual_chunk_1_3_28, residual_chunk_1_3_29, residual_chunk_1_3_30, residual_chunk_1_3_31, residual_chunk_1_3_32, residual_chunk_1_3_33, residual_chunk_1_3_34, residual_chunk_1_3_35, residual_chunk_1_3_36]

end LiteralP13HodgeCertificate
end GroupApproximation
