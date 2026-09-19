import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (3, 0). -/

theorem residual_chunk_3_0_0 : initialChunk 3 0 0 = 69550403 := by
  decide

theorem residual_chunk_3_0_1 : initialChunk 3 0 1 = 210794628 := by
  decide

theorem residual_chunk_3_0_2 : initialChunk 3 0 2 = 82112585 := by
  decide

theorem residual_chunk_3_0_3 : initialChunk 3 0 3 = 540215018 := by
  decide

theorem residual_chunk_3_0_4 : initialChunk 3 0 4 = 192672038 := by
  decide

theorem residual_chunk_3_0_5 : initialChunk 3 0 5 = 299811766 := by
  decide

theorem residual_chunk_3_0_6 : initialChunk 3 0 6 = 224905669 := by
  decide

theorem residual_chunk_3_0_7 : initialChunk 3 0 7 = 249788422 := by
  decide

theorem residual_chunk_3_0_8 : initialChunk 3 0 8 = 316174846 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_0_0 : initialPart 3 0 0 = 2186025375 := by
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
  rw [residual_chunk_3_0_0, residual_chunk_3_0_1, residual_chunk_3_0_2, residual_chunk_3_0_3, residual_chunk_3_0_4, residual_chunk_3_0_5, residual_chunk_3_0_6, residual_chunk_3_0_7, residual_chunk_3_0_8]

end LiteralP13HodgeCertificate
end GroupApproximation
