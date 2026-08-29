import GroupApproximation.Kazhdan.Kazhdan

/-!
# Converse displacement criteria for Kazhdan pairs

The definition of a Kazhdan pair quantifies over representations which admit
an almost invariant unit vector.  Sum-of-squares and spectral-gap arguments
naturally prove the contrapositive statement: in every representation with no
nonzero invariant vector, every unit vector is moved by at least the Kazhdan
tolerance.

This file proves that the two formulations are equivalent.  Keeping this
bridge explicit prevents a group-ring certificate from being connected to
property `(T)` by an unformalized contrapositive argument.
-/

namespace GroupApproximation
namespace IsKazhdanPair

universe u v

variable {G : Type u} [Group G] {Q : Finset G} {ε : ℝ}

/-- A positive uniform displacement bound on representations without
invariant vectors is a Kazhdan pair. -/
theorem of_noInvariant_displacement
    (hε : 0 < ε)
    (hmove :
      ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [CompleteSpace E],
        ∀ ρ : G →* (E ≃ₗᵢ[ℝ] E),
          HasNoInvariantVectors G ρ →
          ∀ x : E, ‖x‖ = 1 →
            ∃ q ∈ Q, ε ≤ ‖ρ q x - x‖) :
    IsKazhdanPair.{u, v} G Q ε := by
  refine ⟨hε, ?_⟩
  intro E _ _ _ ρ x hx hnear
  classical
  by_cases hinv : ∃ y : E, y ≠ 0 ∧ ∀ g : G, ρ g y = y
  · exact hinv
  · have hno : HasNoInvariantVectors G ρ := by
      intro y hy
      by_contra hy0
      exact hinv ⟨y, hy0, hy⟩
    obtain ⟨q, hq, hfar⟩ := hmove E ρ hno x hx
    exact False.elim ((not_lt_of_ge hfar) (hnear q hq))

/-- Homogeneous uniform displacement bounds on representations without
invariant vectors also characterize Kazhdan pairs. -/
theorem of_noInvariant_displacement_mul_norm
    (hε : 0 < ε)
    (hmove :
      ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [CompleteSpace E],
        ∀ ρ : G →* (E ≃ₗᵢ[ℝ] E),
          HasNoInvariantVectors G ρ →
          ∀ x : E, x ≠ 0 →
            ∃ q ∈ Q, ε * ‖x‖ ≤ ‖ρ q x - x‖) :
    IsKazhdanPair.{u, v} G Q ε := by
  apply of_noInvariant_displacement hε
  intro E _ _ _ ρ hno x hx
  have hx0 : x ≠ 0 := fun hzero ↦ by simp [hzero] at hx
  obtain ⟨q, hq, hfar⟩ := hmove E ρ hno x hx0
  exact ⟨q, hq, by simpa [hx] using hfar⟩

end IsKazhdanPair
end GroupApproximation
