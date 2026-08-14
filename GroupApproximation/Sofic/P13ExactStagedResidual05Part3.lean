import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--36 for residual block (0, 5). -/

theorem residual_chunk_0_5_27 : initialChunk 0 5 27 = 325754641 := by
  decide

theorem residual_chunk_0_5_28 : initialChunk 0 5 28 = 119939107 := by
  decide

theorem residual_chunk_0_5_29 : initialChunk 0 5 29 = 256119426 := by
  decide

theorem residual_chunk_0_5_30 : initialChunk 0 5 30 = 151294078 := by
  decide

theorem residual_chunk_0_5_31 : initialChunk 0 5 31 = 193440905 := by
  decide

theorem residual_chunk_0_5_32 : initialChunk 0 5 32 = 127797119 := by
  decide

theorem residual_chunk_0_5_33 : initialChunk 0 5 33 = 322486550 := by
  decide

theorem residual_chunk_0_5_34 : initialChunk 0 5 34 = 138048725 := by
  decide

theorem residual_chunk_0_5_35 : initialChunk 0 5 35 = 107991156 := by
  decide

theorem residual_chunk_0_5_36 : finalChunk 0 5 = 98498859 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_5_3 : initialPart 0 5 3 + finalChunk 0 5 = 1841370566 := by
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
  rw [residual_chunk_0_5_27, residual_chunk_0_5_28, residual_chunk_0_5_29, residual_chunk_0_5_30, residual_chunk_0_5_31, residual_chunk_0_5_32, residual_chunk_0_5_33, residual_chunk_0_5_34, residual_chunk_0_5_35, residual_chunk_0_5_36]

end LiteralP13HodgeCertificate
end GroupApproximation

