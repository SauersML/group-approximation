import GroupApproximation.Kazhdan.KazhdanOrthogonal

/-!
# Fixed-space propagation under a one-sided compressor

If `t * ι(Γ) * t⁻¹ ⊆ ι(Γ)`, then every vector fixed by `ι(Γ)` is the
`ρ(t)`-translate of another `ι(Γ)`-fixed vector.  Equivalently,

`Fix(ρ ∘ ι) ⊆ ρ(t) Fix(ρ ∘ ι)`.

This is the Hilbert-space inclusion behind the order identity for the
Kazhdan projection in the non-MF argument.  It is also a direct
operator-representation analogue of the Mautner-type fixed-space propagation
isolated in OpenAI Proposition 2.3 and Kun--Thom, arXiv:2608.06222.  The proof
below is native Lean code and copies no external implementation.
-/

namespace GroupApproximation
namespace FixedSpaceCompression

universe u v w

variable {Γ : Type u} [Group Γ]
variable {H : Type v} [Group H]
variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A one-sided compressor propagates fixed vectors in the direction used by
the Kazhdan projection order argument.  The witness is explicitly
`y = ρ(t⁻¹) x`. -/
theorem exists_invariant_preimage
    (ρ : H →* (E ≃ₗᵢ[ℝ] E)) (ι : Γ →* H) (t : H)
    (compresses : ∀ γ : Γ, ∃ δ : Γ, t * ι γ * t⁻¹ = ι δ)
    {x : E}
    (hx : x ∈ KazhdanOrthogonal.invariantSubmodule (ρ.comp ι)) :
    ∃ y : E,
      y ∈ KazhdanOrthogonal.invariantSubmodule (ρ.comp ι) ∧ ρ t y = x := by
  let y : E := ρ t⁻¹ x
  refine ⟨y, ?_, ?_⟩
  · rw [KazhdanOrthogonal.mem_invariantSubmodule]
    intro γ
    obtain ⟨δ, hδ⟩ := compresses γ
    have hxδ : ρ (ι δ) x = x :=
      (KazhdanOrthogonal.mem_invariantSubmodule (ρ.comp ι) x).mp hx δ
    calc
      ρ (ι γ) y = ρ t⁻¹ (ρ (t * ι γ * t⁻¹) x) := by
        simp [y]
      _ = ρ t⁻¹ (ρ (ι δ) x) := by rw [hδ]
      _ = y := by rw [hxδ]
  · simp [y]

/-- Submodule form of `exists_invariant_preimage`: the fixed subspace is
contained in its `ρ(t)`-translate. -/
theorem invariantSubmodule_le_map
    (ρ : H →* (E ≃ₗᵢ[ℝ] E)) (ι : Γ →* H) (t : H)
    (compresses : ∀ γ : Γ, ∃ δ : Γ, t * ι γ * t⁻¹ = ι δ) :
    KazhdanOrthogonal.invariantSubmodule (ρ.comp ι) ≤
      (KazhdanOrthogonal.invariantSubmodule (ρ.comp ι)).map
        (ρ t).toLinearEquiv.toLinearMap := by
  intro x hx
  obtain ⟨y, hy, hty⟩ := exists_invariant_preimage ρ ι t compresses hx
  exact ⟨y, hy, hty⟩

end FixedSpaceCompression
end GroupApproximation
