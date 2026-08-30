import GroupApproximation.Analysis.VoiculescuGlimmCombination

/-!
# (V2) The expansion of a quadratic form at a superposition

The last step of Glimm's lemma turns a convex combination of vector states back
into a single vector state.  The vector is the superposition `ξ = ∑ cᵢ ξᵢ` with
`cᵢ = √tᵢ`, and everything depends on what its quadratic form is:

    `⟪a ξ, ξ⟫ = ∑ᵢ ∑ⱼ cᵢ cⱼ ⟪a ξᵢ, ξⱼ⟫` ,

the diagonal terms `cᵢ² ⟪a ξᵢ, ξᵢ⟫` reproducing the convex combination and the
off-diagonal terms being the error the construction has to make small.  This
module proves that identity and the exact case, and stops there: choosing the
`ξᵢ` so the cross terms vanish approximately is the next stage.

Real coefficients are what keep it clean — the inner product conjugates its
first slot, so complex `cᵢ` would leave `conj(cᵢ) cⱼ` and the diagonal would no
longer be `|cᵢ|²` times a real number.  Since `cᵢ = √tᵢ`, real is all that is
needed.

## The exact case is the model test

`inner_sum_smul_of_inner_eq_zero` is not a corollary anyone needs: it is the
test that the expansion above is right.  If the cross terms vanish exactly then
the form must be exactly `∑ cᵢ² ⟪a ξᵢ, ξᵢ⟫` — the convex combination, with no
correction.  A dropped conjugate, a wrong index in the double sum, or a factor
of two in the off-diagonal all survive an inhabitation check and all fail this
one.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace
open scoped ComplexOrder

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **The expansion.**  The quadratic form of an operator at a real
superposition is the double sum of its matrix entries against the coefficients. -/
theorem inner_sum_smul_expand {n : ℕ} (c : Fin n → ℝ) (ξ : Fin n → H)
    (a : H →L[ℂ] H) :
    ⟪a (∑ i, ((c i : ℝ) : ℂ) • ξ i), ∑ i, ((c i : ℝ) : ℂ) • ξ i⟫_ℂ
      = ∑ i, ∑ j, ((c i * c j : ℝ) : ℂ) * ⟪a (ξ i), ξ j⟫_ℂ := by
  have happly : a (∑ i, ((c i : ℝ) : ℂ) • ξ i)
      = ∑ i, ((c i : ℝ) : ℂ) • a (ξ i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul]
  rw [happly, sum_inner]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [inner_smul_left, Complex.conj_ofReal, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [inner_smul_right, Complex.ofReal_mul]
  ring

/-- **The exact case, and the model test of the expansion.**  When the cross
terms vanish the form is exactly the weighted sum of the diagonal ones — the
convex combination the construction is trying to reproduce. -/
theorem inner_sum_smul_of_inner_eq_zero {n : ℕ} (c : Fin n → ℝ) (ξ : Fin n → H)
    (a : H →L[ℂ] H) (hzero : ∀ i j, i ≠ j → ⟪a (ξ i), ξ j⟫_ℂ = 0) :
    ⟪a (∑ i, ((c i : ℝ) : ℂ) • ξ i), ∑ i, ((c i : ℝ) : ℂ) • ξ i⟫_ℂ
      = ∑ i, ((c i * c i : ℝ) : ℂ) * ⟪a (ξ i), ξ i⟫_ℂ := by
  rw [inner_sum_smul_expand]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  refine Finset.sum_eq_single i (fun j _ hj ↦ ?_) (fun h ↦ absurd (Finset.mem_univ i) h)
  rw [hzero i j (fun hij ↦ hj hij.symm), mul_zero]

/-- The squared norm of a superposition of orthonormal vectors, as the same
expansion at the identity. -/
theorem inner_self_sum_smul_of_inner_eq_zero {n : ℕ} (c : Fin n → ℝ)
    (ξ : Fin n → H) (hzero : ∀ i j, i ≠ j → ⟪ξ i, ξ j⟫_ℂ = 0) :
    ⟪∑ i, ((c i : ℝ) : ℂ) • ξ i, ∑ i, ((c i : ℝ) : ℂ) • ξ i⟫_ℂ
      = ∑ i, ((c i * c i : ℝ) : ℂ) * ⟪ξ i, ξ i⟫_ℂ :=
  inner_sum_smul_of_inner_eq_zero c ξ 1 hzero

end

end ShulmanFill
end GroupApproximation
