import GroupApproximation.Analysis.VoiculescuGlimmState

/-!
# (V2) The functional's shape: from a positive linear map to the assembly's hypotheses

`GlimmLemmaStatement` hands its state over as a `↥A →ₚ[ℂ] ℂ` — a bundled
positive linear map — while `Analysis/VoiculescuGlimmState` consumes a plain
linear map together with an explicit positivity hypothesis in the shape
`StateExtension` uses, "sends ambient positives to nonnegative reals".  This
module is the bridge, and it is not a coercion.

Three things have to line up.  The order on `↥A` is the `Subtype` order, so it
*is* the restriction of the Loewner order on `B(H)` — `Subtype.coe_le_coe` is
the whole content of that step, but it is a step.  Positivity of `φ` is
monotonicity of its underlying order homomorphism, which gives `0 ≤ φ b` in `ℂ`
rather than a nonnegative real.  And `0 ≤ z` in `ComplexOrder` means
`0 ≤ z.re ∧ z.im = 0`, which is what turns it into the real number the
extension theorem wants.

## Unitality, which would otherwise have been a fourth seam

The assembly's conclusion does not mention `ρ 1`, but everything downstream —
the spectral bound, the connector — needs `ρ 1 = 1`.  It is free here and
nowhere else: `ρ` agrees with `φ` on `A`, `1 ∈ A`, and `φ 1 = 1` is a hypothesis
of the statement.  So the packaged theorem below carries it, rather than leaving
each consumer to rediscover that it can be recovered.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace
open scoped ComplexOrder

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **A positive linear map sends ambient positives to nonnegative reals.**
The order on the subalgebra is the restriction of the Loewner order, and
`0 ≤ z` in `ℂ` says `z` is a nonnegative real. -/
theorem exists_nonneg_apply_of_positive {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (φ : ↥A →ₚ[ℂ] ℂ) {b : ↥A} (hb : 0 ≤ (b : H →L[ℂ] H)) :
    ∃ r : ℝ, 0 ≤ r ∧ φ b = r := by
  have hb' : (0 : ↥A) ≤ b := by
    rw [← Subtype.coe_le_coe, ZeroMemClass.coe_zero]
    exact hb
  have h0 : (0 : ℂ) ≤ φ b := by
    have hmono := φ.toOrderHom.monotone hb'
    rwa [map_zero] at hmono
  obtain ⟨hre, him⟩ := Complex.le_def.mp h0
  refine ⟨(φ b).re, ?_, ?_⟩
  · rw [Complex.zero_re] at hre
    exact hre
  · refine Complex.ext ?_ ?_
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im, ← him, Complex.zero_im]

/-- **The state, in the shape the rest of (V2) consumes.**  A positive unital
functional on `A` extends to a positive unital functional on `B(H)` that
annihilates the compacts.

This is `Analysis/VoiculescuGlimmState.exists_extension_annihilating_compacts`
with the `→ₚ[ℂ]` interface of `GlimmLemmaStatement` on the front and unitality
carried through on the back. -/
theorem exists_state_of_positiveLinearMap {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hA : IsClosed (A : Set (H →L[ℂ] H)))
    (hAK : ∀ T ∈ A, IsCompactOperator T → T = 0)
    (φ : ↥A →ₚ[ℂ] ℂ) (hone : φ 1 = 1) :
    ∃ ρ : (H →L[ℂ] H) →ₗ[ℂ] ℂ,
      (∀ b : ↥A, ρ (b : H →L[ℂ] H) = φ b) ∧
      (∀ T : H →L[ℂ] H, IsCompactOperator T → ρ T = 0) ∧
      (∀ T : H →L[ℂ] H, 0 ≤ T → ∃ r : ℝ, 0 ≤ r ∧ ρ T = r) ∧
      ρ 1 = 1 := by
  obtain ⟨ρ, hρA, hρK, hρpos⟩ :=
    exists_extension_annihilating_compacts hA hAK φ.toLinearMap
      (fun b hb ↦ exists_nonneg_apply_of_positive φ hb)
  refine ⟨ρ, hρA, hρK, hρpos, ?_⟩
  have h1 := hρA 1
  rw [OneMemClass.coe_one] at h1
  rw [h1]
  exact hone

end

end ShulmanFill
end GroupApproximation
