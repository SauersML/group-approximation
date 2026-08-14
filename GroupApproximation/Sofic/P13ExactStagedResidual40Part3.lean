import GroupApproximation.Sofic.P13ExactStagedCertificateCore

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Direct kernel checks 27--36 for residual block (4, 0). -/

theorem residual_chunk_4_0_27 : initialChunk 4 0 27 = 283646954 := by
  decide

theorem residual_chunk_4_0_28 : initialChunk 4 0 28 = 140256977 := by
  decide

theorem residual_chunk_4_0_29 : initialChunk 4 0 29 = 329678329 := by
  decide

theorem residual_chunk_4_0_30 : initialChunk 4 0 30 = 134624353 := by
  decide

theorem residual_chunk_4_0_31 : initialChunk 4 0 31 = 125475365 := by
  decide

theorem residual_chunk_4_0_32 : initialChunk 4 0 32 = 135220714 := by
  decide

theorem residual_chunk_4_0_33 : initialChunk 4 0 33 = 169338349 := by
  decide

theorem residual_chunk_4_0_34 : initialChunk 4 0 34 = 185262615 := by
  decide

theorem residual_chunk_4_0_35 : initialChunk 4 0 35 = 40906321 := by
  decide

theorem residual_chunk_4_0_36 : finalChunk 4 0 = 64055327 := by
  decide

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_0_3 : initialPart 4 0 3 + finalChunk 4 0 = 1608465304 := by
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
  rw [residual_chunk_4_0_27, residual_chunk_4_0_28, residual_chunk_4_0_29, residual_chunk_4_0_30, residual_chunk_4_0_31, residual_chunk_4_0_32, residual_chunk_4_0_33, residual_chunk_4_0_34, residual_chunk_4_0_35, residual_chunk_4_0_36]

end LiteralP13HodgeCertificate
end GroupApproximation

