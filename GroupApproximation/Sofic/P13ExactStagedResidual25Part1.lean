import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (2, 5). -/

theorem residual_chunk_2_5_9 : initialChunk 2 5 9 = 221826710 := by
  decide

theorem residual_chunk_2_5_10 : initialChunk 2 5 10 = 167126460 := by
  decide

theorem residual_chunk_2_5_11 : initialChunk 2 5 11 = 103249566 := by
  decide

theorem residual_chunk_2_5_12 : initialChunk 2 5 12 = 248720758 := by
  decide

theorem residual_chunk_2_5_13 : initialChunk 2 5 13 = 317599639 := by
  decide

theorem residual_chunk_2_5_14 : initialChunk 2 5 14 = 125075105 := by
  decide

theorem residual_chunk_2_5_15 : initialChunk 2 5 15 = 89306032 := by
  decide

theorem residual_chunk_2_5_16 : initialChunk 2 5 16 = 197738650 := by
  decide

theorem residual_chunk_2_5_17 : initialChunk 2 5 17 = 171638870 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_5_1 : initialPart 2 5 1 = 1642281790 := by
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
  rw [residual_chunk_2_5_9, residual_chunk_2_5_10, residual_chunk_2_5_11, residual_chunk_2_5_12, residual_chunk_2_5_13, residual_chunk_2_5_14, residual_chunk_2_5_15, residual_chunk_2_5_16, residual_chunk_2_5_17]

end LiteralP13HodgeCertificate
end GroupApproximation

