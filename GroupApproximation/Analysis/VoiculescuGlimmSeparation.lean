import GroupApproximation.Analysis.VoiculescuGlimmCombination
import Mathlib.Algebra.Star.BigOperators

/-!
# (V2) The separation: the state's values lie among the vector states

This is where Glimm's lemma becomes a statement about one finite family at a
time.  The state `ρ` and the vector states at unit vectors of `Vᗮ` all give
points of `ℝⁿ` — the tuples of their values on a family of self-adjoint
operators — and the claim is that `ρ`'s point lies in the closed convex hull of
theirs.

The proof is Hahn–Banach against the connector.  If it did not, a real-linear
functional would separate: some `∑ αᵢ xᵢ` would be `< u` at every vector state
and `> u` at `ρ`.  But a real functional on `ℝⁿ` is a real combination of
coordinates, and a real combination of coordinates is the quadratic form of
`b = ∑ αᵢ aᵢ`, which is self-adjoint because the `aᵢ` are and the `αᵢ` are real.
So the separation says exactly that `re ⟪b ξ, ξ⟫ < u` on `Vᗮ` while
`re ρ(b) > u` — and the connector says the first forces the second false.

## Why the family is self-adjoint

A general family would put the tuples in `ℂⁿ`, and the separating functional
would produce `b = ∑ (αᵢ + i βᵢ) aᵢ`, which is not self-adjoint; the connector
would then need its self-adjoint part, and relating `ρ(b)` to `ρ((b + b⋆)/2)`
needs `ρ` to be `⋆`-preserving — true for positive functionals, but a separate
theorem.  Restricting to self-adjoint families makes every tuple real, `b`
self-adjoint on the nose, and that obligation vanishes.  The reduction from a
general finite set is `a = ℜa + i ℑa`, and it belongs to the consumer.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace
open scoped ComplexOrder

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A `Pi.single` with a scalar entry is that scalar times the standard one. -/
theorem pi_single_eq_smul {n : ℕ} (i : Fin n) (c : ℝ) :
    Pi.single i c = c • Pi.single i (1 : ℝ) := by
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

/-- A continuous real functional on `Fin n → ℝ` is the combination of
coordinates with the coefficients it takes at the standard vectors. -/
theorem apply_eq_sum_smul {n : ℕ} (f : (Fin n → ℝ) →L[ℝ] ℝ) (x : Fin n → ℝ) :
    f x = ∑ i, x i * f (Pi.single i (1 : ℝ)) := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [pi_single_eq_smul, map_smul, smul_eq_mul]

/-- **The separation.**  The tuple of the state's values lies in the closed
convex hull of the tuples of the vector states at unit vectors orthogonal to
`V`. -/
theorem mem_closure_convexHull_vectorStates
    (ρ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hpos : ∀ T : H →L[ℂ] H, 0 ≤ T → ∃ r : ℝ, 0 ≤ r ∧ ρ T = r)
    (hone : ρ 1 = 1) (hK : ∀ T : H →L[ℂ] H, IsCompactOperator T → ρ T = 0)
    (V : Submodule ℂ H) [FiniteDimensional ℂ V]
    {n : ℕ} (a : Fin n → (H →L[ℂ] H)) (hsa : ∀ i, IsSelfAdjoint (a i)) :
    (fun i ↦ (ρ (a i)).re) ∈ closure (convexHull ℝ
      {x : Fin n → ℝ | ∃ ξ : H, ξ ∈ Vᗮ ∧ ‖ξ‖ = 1 ∧
        ∀ i, x i = (⟪a i ξ, ξ⟫_ℂ).re}) := by
  by_contra hcon
  obtain ⟨f, u, hlt, hgt⟩ := geometric_hahn_banach_closed_point
    ((convex_convexHull ℝ _).closure) isClosed_closure hcon
  set α : Fin n → ℝ := fun i ↦ f (Pi.single i (1 : ℝ)) with hαdef
  set b : H →L[ℂ] H := ∑ i, ((α i : ℝ) : ℂ) • a i with hbdef
  have hbsa : IsSelfAdjoint b := by
    rw [hbdef]
    refine isSelfAdjoint_sum _ fun i _ ↦ ?_
    show star _ = _
    rw [star_smul, Complex.conj_ofReal, (hsa i).star_eq]
  have hvec : ∀ ξ : H, ξ ∈ Vᗮ → ‖ξ‖ = 1 → (⟪b ξ, ξ⟫_ℂ).re ≤ u := by
    intro ξ hξ hunit
    have hmemS : (fun i ↦ (⟪a i ξ, ξ⟫_ℂ).re) ∈ closure (convexHull ℝ
        {x : Fin n → ℝ | ∃ ξ : H, ξ ∈ Vᗮ ∧ ‖ξ‖ = 1 ∧
          ∀ i, x i = (⟪a i ξ, ξ⟫_ℂ).re}) :=
      subset_closure (subset_convexHull ℝ _ ⟨ξ, hξ, hunit, fun i ↦ rfl⟩)
    have hf := hlt _ hmemS
    rw [apply_eq_sum_smul] at hf
    rw [hbdef, re_inner_sum_smul]
    refine le_of_lt (lt_of_le_of_lt (le_of_eq ?_) hf)
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  have hle := re_apply_le_of_inner_le ρ hpos hone hK V hbsa
    (re_inner_le_sq_of_unit hvec)
  have hρb : (ρ b).re = ∑ i, α i * (ρ (a i)).re := by
    rw [hbdef, map_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, smul_eq_mul, Complex.re_ofReal_mul]
  rw [hρb] at hle
  rw [apply_eq_sum_smul] at hgt
  have hcomm : ∑ i, (ρ (a i)).re * α i = ∑ i, α i * (ρ (a i)).re :=
    Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  rw [hcomm] at hgt
  exact absurd hle (not_le.mpr hgt)

end

end ShulmanFill
end GroupApproximation
