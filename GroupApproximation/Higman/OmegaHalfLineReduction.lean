import GroupApproximation.Higman.EnumeratedRange
import GroupApproximation.Higman.OmegaClosure

/-!
# Reducing Omega to two one-sided block closures

The refuted modified Mikaelian tower uses a two-sided outer shift.  Its bad
word is created when a block at the origin is inserted on the wrong side of a
conjugator supported to the left.  A replacement may instead construct the
nonnegative and negative block conditions separately and intersect them.

This file makes that route exact.  It is more than a set-theoretic slogan:
`ASub_inter` turns the intersection of the two sequence predicates into the
intersection of their coded subgroups, and benign subgroups are closed under
that intersection.  Thus only two genuinely one-sided constructions remain.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Seq

/-- The global block condition is exactly the conjunction of its two
half-line restrictions. -/
theorem omegaOp_eq_omegaGE_inter_omegaLT (m : ℕ) (B : Set E) :
    omegaOp m B = omegaGE m B ∩ omegaLT m B := by
  ext f
  constructor
  · intro hf
    exact ⟨fun i _ => hf i, fun i _ => hf i⟩
  · rintro ⟨hge, hlt⟩ i
    by_cases hi : 0 ≤ i
    · exact hge i hi
    · exact hlt i (by omega)

/-- The exact replacement input suggested by the order obstruction: build
each half-line using a genuinely one-sided tower. -/
structure HalfLineInput : Prop where
  nonnegative : ∀ (m : ℕ), 0 < m → ∀ (B : Set E), (0 : E) ∈ B →
    BenignTF (ASub B) → BenignTF (ASub (omegaGE m B))
  negative : ∀ (m : ℕ), 0 < m → ∀ (B : Set E), (0 : E) ∈ B →
    BenignTF (ASub B) → BenignTF (ASub (omegaLT m B))

/-- **Two one-sided Omega constructions suffice for the full operation.** -/
theorem omegaInput_of_halfLine (h : HalfLineInput) : OmegaInput := by
  refine ⟨fun m hm B h0 hB => ?_⟩
  rw [omegaOp_eq_omegaGE_inter_omegaLT, ASub_inter]
  exact BenignTF.inf (h.nonnegative m hm B h0 hB)
    (h.negative m hm B h0 hB)

end Omega
end Higman
end GroupApproximation
