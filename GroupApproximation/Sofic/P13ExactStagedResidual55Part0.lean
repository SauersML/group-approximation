import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (5, 5). -/

theorem residual_chunk_5_5_0 : initialChunk 5 5 0 = 150141857 := by
  decide

theorem residual_chunk_5_5_1 : initialChunk 5 5 1 = 198872667 := by
  decide

theorem residual_chunk_5_5_2 : initialChunk 5 5 2 = 318606121 := by
  decide

theorem residual_chunk_5_5_3 : initialChunk 5 5 3 = 311004036 := by
  decide

theorem residual_chunk_5_5_4 : initialChunk 5 5 4 = 140310669 := by
  decide

theorem residual_chunk_5_5_5 : initialChunk 5 5 5 = 212192255 := by
  decide

theorem residual_chunk_5_5_6 : initialChunk 5 5 6 = 163569929 := by
  decide

theorem residual_chunk_5_5_7 : initialChunk 5 5 7 = 117647462 := by
  decide

theorem residual_chunk_5_5_8 : initialChunk 5 5 8 = 110407087 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_5_0 : initialPart 5 5 0 = 1722752083 := by
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
  rw [residual_chunk_5_5_0, residual_chunk_5_5_1, residual_chunk_5_5_2, residual_chunk_5_5_3, residual_chunk_5_5_4, residual_chunk_5_5_5, residual_chunk_5_5_6, residual_chunk_5_5_7, residual_chunk_5_5_8]

end LiteralP13HodgeCertificate
end GroupApproximation

