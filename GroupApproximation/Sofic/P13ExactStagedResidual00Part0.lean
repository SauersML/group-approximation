import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 0--8 for residual block (0, 0). -/

theorem residual_chunk_0_0_0 : initialChunk 0 0 0 = 318517786 := by
  decide

theorem residual_chunk_0_0_1 : initialChunk 0 0 1 = 393139355 := by
  decide

theorem residual_chunk_0_0_2 : initialChunk 0 0 2 = 406863868 := by
  decide

theorem residual_chunk_0_0_3 : initialChunk 0 0 3 = 624023378 := by
  decide

theorem residual_chunk_0_0_4 : initialChunk 0 0 4 = 329826921 := by
  decide

theorem residual_chunk_0_0_5 : initialChunk 0 0 5 = 371347241 := by
  decide

theorem residual_chunk_0_0_6 : initialChunk 0 0 6 = 394680694 := by
  decide

theorem residual_chunk_0_0_7 : initialChunk 0 0 7 = 349299800 := by
  decide

theorem residual_chunk_0_0_8 : initialChunk 0 0 8 = 329965950 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_0_0 : initialPart 0 0 0 = 3517664993 := by
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
  rw [residual_chunk_0_0_0, residual_chunk_0_0_1, residual_chunk_0_0_2,
    residual_chunk_0_0_3, residual_chunk_0_0_4, residual_chunk_0_0_5,
    residual_chunk_0_0_6, residual_chunk_0_0_7, residual_chunk_0_0_8]

end LiteralP13HodgeCertificate
end GroupApproximation
