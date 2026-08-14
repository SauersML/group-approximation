import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 9--17 for residual block (5, 4). -/

theorem residual_chunk_5_4_9 : initialChunk 5 4 9 = 331732571 := by
  decide

theorem residual_chunk_5_4_10 : initialChunk 5 4 10 = 129803268 := by
  decide

theorem residual_chunk_5_4_11 : initialChunk 5 4 11 = 166157789 := by
  decide

theorem residual_chunk_5_4_12 : initialChunk 5 4 12 = 345009166 := by
  decide

theorem residual_chunk_5_4_13 : initialChunk 5 4 13 = 131938671 := by
  decide

theorem residual_chunk_5_4_14 : initialChunk 5 4 14 = 151573772 := by
  decide

theorem residual_chunk_5_4_15 : initialChunk 5 4 15 = 78707784 := by
  decide

theorem residual_chunk_5_4_16 : initialChunk 5 4 16 = 236813372 := by
  decide

theorem residual_chunk_5_4_17 : initialChunk 5 4 17 = 399282244 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_4_1 : initialPart 5 4 1 = 1971018637 := by
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
  rw [residual_chunk_5_4_9, residual_chunk_5_4_10, residual_chunk_5_4_11, residual_chunk_5_4_12, residual_chunk_5_4_13, residual_chunk_5_4_14, residual_chunk_5_4_15, residual_chunk_5_4_16, residual_chunk_5_4_17]

end LiteralP13HodgeCertificate
end GroupApproximation

