import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (3, 3). -/

theorem residual_chunk_3_3_9 : initialChunk 3 3 9 = 240087725 := by
  decide

theorem residual_chunk_3_3_10 : initialChunk 3 3 10 = 184671580 := by
  decide

theorem residual_chunk_3_3_11 : initialChunk 3 3 11 = 268241276 := by
  decide

theorem residual_chunk_3_3_12 : initialChunk 3 3 12 = 200900016 := by
  decide

theorem residual_chunk_3_3_13 : initialChunk 3 3 13 = 136938499 := by
  decide

theorem residual_chunk_3_3_14 : initialChunk 3 3 14 = 55845489 := by
  decide

theorem residual_chunk_3_3_15 : initialChunk 3 3 15 = 77749917 := by
  decide

theorem residual_chunk_3_3_16 : initialChunk 3 3 16 = 102243649 := by
  decide

theorem residual_chunk_3_3_17 : initialChunk 3 3 17 = 111299992 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_3_1 : initialPart 3 3 1 = 1377978143 := by
  unfold initialPart
  rw [sum_fin9_explicit]
  rw [show finProdFinEquiv ((1 : Fin 4), (0 : Fin 9)) = (9 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (1 : Fin 9)) = (10 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (2 : Fin 9)) = (11 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (3 : Fin 9)) = (12 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (4 : Fin 9)) = (13 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (5 : Fin 9)) = (14 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (6 : Fin 9)) = (15 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (7 : Fin 9)) = (16 : Fin 36) by decide]
  rw [show finProdFinEquiv ((1 : Fin 4), (8 : Fin 9)) = (17 : Fin 36) by decide]
  rw [residual_chunk_3_3_9, residual_chunk_3_3_10, residual_chunk_3_3_11, residual_chunk_3_3_12, residual_chunk_3_3_13, residual_chunk_3_3_14, residual_chunk_3_3_15, residual_chunk_3_3_16, residual_chunk_3_3_17]

end LiteralP13HodgeCertificate
end GroupApproximation
