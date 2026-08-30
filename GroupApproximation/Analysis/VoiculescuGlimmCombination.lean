import GroupApproximation.Analysis.VoiculescuGlimmConnector

/-!
# (V2) Real combinations of operators, read on vectors

The separation step of Glimm's lemma produces a real-linear functional on the
tuple space and has to read it back as a single operator.  Two facts do that,
and they are the arithmetic of the step rather than its content, so they are
proved here and spent there.

The first says what a real combination `∑ αᵢ aᵢ` does to a vector: its quadratic
form is the real combination of the individual forms.  Real coefficients are
what makes this clean — the inner product is conjugate-linear in its first slot,
so complex coefficients would conjugate, and the combination would not be
self-adjoint either.

The second is the scaling that turns a statement about unit vectors into a
statement about all vectors, since the separation naturally speaks of unit
vectors while the connector wants every vector of `Vᗮ`.  The `‖ξ‖²` on the right
is exactly the homogeneity of a quadratic form, and the zero vector is the one
case worth checking separately.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace
open scoped ComplexOrder

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **A real combination of operators, read on a vector.**  The quadratic form
of `∑ αᵢ aᵢ` is `∑ αᵢ` times the individual quadratic forms. -/
theorem re_inner_sum_smul {n : ℕ} (α : Fin n → ℝ) (a : Fin n → (H →L[ℂ] H))
    (ξ : H) :
    (⟪(∑ i, ((α i : ℝ) : ℂ) • a i) ξ, ξ⟫_ℂ).re
      = ∑ i, α i * (⟪a i ξ, ξ⟫_ℂ).re := by
  have happly : (∑ i, ((α i : ℝ) : ℂ) • a i) ξ
      = ∑ i, ((α i : ℝ) : ℂ) • (a i ξ) := by
    rw [show ((∑ i, ((α i : ℝ) : ℂ) • a i) ξ)
        = (ContinuousLinearMap.apply ℂ H ξ) (∑ i, ((α i : ℝ) : ℂ) • a i) from rfl,
      map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ rfl
  rw [happly, sum_inner, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [inner_smul_left, Complex.conj_ofReal, Complex.re_ofReal_mul]

/-- **From unit vectors to all vectors.**  A bound on the quadratic form over
unit vectors of `Vᗮ` is the homogeneous bound over all of `Vᗮ`, which is the
shape the connector consumes. -/
theorem re_inner_le_sq_of_unit {b : H →L[ℂ] H} {V : Submodule ℂ H} {t : ℝ}
    (h : ∀ ξ : H, ξ ∈ Vᗮ → ‖ξ‖ = 1 → (⟪b ξ, ξ⟫_ℂ).re ≤ t) (ξ : H)
    (hξ : ξ ∈ Vᗮ) : (⟪b ξ, ξ⟫_ℂ).re ≤ t * ‖ξ‖ ^ 2 := by
  rcases eq_or_ne ξ 0 with rfl | hne
  · simp
  · have hcpos : (0 : ℝ) < ‖ξ‖ := norm_pos_iff.mpr hne
    have hsq : (0 : ℝ) < ‖ξ‖ ^ 2 := by positivity
    have hunit : ‖((‖ξ‖⁻¹ : ℝ) : ℂ) • ξ‖ = 1 := norm_smul_inv_norm hne
    have hmem : ((‖ξ‖⁻¹ : ℝ) : ℂ) • ξ ∈ Vᗮ := Vᗮ.smul_mem _ hξ
    have hval := h _ hmem hunit
    have hkey : ⟪b (((‖ξ‖⁻¹ : ℝ) : ℂ) • ξ), ((‖ξ‖⁻¹ : ℝ) : ℂ) • ξ⟫_ℂ
        = (((‖ξ‖⁻¹ * ‖ξ‖⁻¹ : ℝ)) : ℂ) * ⟪b ξ, ξ⟫_ℂ := by
      rw [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
        Complex.ofReal_mul]
      ring
    rw [hkey, Complex.re_ofReal_mul] at hval
    have hinv : ‖ξ‖⁻¹ * ‖ξ‖⁻¹ = (‖ξ‖ ^ 2)⁻¹ := by
      rw [← mul_inv, ← pow_two]
    rw [hinv, inv_mul_le_iff₀ hsq] at hval
    rw [mul_comm]
    exact hval

end

end ShulmanFill
end GroupApproximation
